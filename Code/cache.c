/* cache.c - cache module routines */

/* SimpleScalar(TM) Tool Suite
 * Copyright (C) 1994-2003 by Todd M. Austin, Ph.D. and SimpleScalar, LLC.
 * All Rights Reserved. 
 * 
 * THIS IS A LEGAL DOCUMENT, BY USING SIMPLESCALAR,
 * YOU ARE AGREEING TO THESE TERMS AND CONDITIONS.
 * 
 * No portion of this work may be used by any commercial entity, or for any
 * commercial purpose, without the prior, written permission of SimpleScalar,
 * LLC (info@simplescalar.com). Nonprofit and noncommercial use is permitted
 * as described below.
 * 
 * 1. SimpleScalar is provided AS IS, with no warranty of any kind, express
 * or implied. The user of the program accepts full responsibility for the
 * application of the program and the use of any results.
 * 
 * 2. Nonprofit and noncommercial use is encouraged. SimpleScalar may be
 * downloaded, compiled, executed, copied, and modified solely for nonprofit,
 * educational, noncommercial research, and noncommercial scholarship
 * purposes provided that this notice in its entirety accompanies all copies.
 * Copies of the modified software can be delivered to persons who use it
 * solely for nonprofit, educational, noncommercial research, and
 * noncommercial scholarship purposes provided that this notice in its
 * entirety accompanies all copies.
 * 
 * 3. ALL COMMERCIAL USE, AND ALL USE BY FOR PROFIT ENTITIES, IS EXPRESSLY
 * PROHIBITED WITHOUT A LICENSE FROM SIMPLESCALAR, LLC (info@simplescalar.com).
 * 
 * 4. No nonprofit user may place any restrictions on the use of this software,
 * including as modified by the user, by any other authorized user.
 * 
 * 5. Noncommercial and nonprofit users may distribute copies of SimpleScalar
 * in compiled or executable form as set forth in Section 2, provided that
 * either: (A) it is accompanied by the corresponding machine-readable source
 * code, or (B) it is accompanied by a written offer, with no time limit, to
 * give anyone a machine-readable copy of the corresponding source code in
 * return for reimbursement of the cost of distribution. This written offer
 * must permit verbatim duplication by anyone, or (C) it is distributed by
 * someone who received only the executable form, and is accompanied by a
 * copy of the written offer of source code.
 * 
 * 6. SimpleScalar was developed by Todd M. Austin, Ph.D. The tool suite is
 * currently maintained by SimpleScalar LLC (info@simplescalar.com). US Mail:
 * 2395 Timbercrest Court, Ann Arbor, MI 48105.
 * 
 * Copyright (C) 1994-2003 by Todd M. Austin, Ph.D. and SimpleScalar, LLC.
 */


#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "host.h"
#include "misc.h"
#include "machine.h"
#include "cache.h"

/* cache access macros */
#define CACHE_TAG(cp, addr)	((addr) >> (cp)->tag_shift)
#define CACHE_SET(cp, addr)	(((addr) >> (cp)->set_shift) & (cp)->set_mask)
#define CACHE_BLK(cp, addr)	((addr) & (cp)->blk_mask)
#define CACHE_TAGSET(cp, addr)	((addr) & (cp)->tagset_mask)

/* extract/reconstruct a block address */
#define CACHE_BADDR(cp, addr)	((addr) & ~(cp)->blk_mask)
#define CACHE_MK_BADDR(cp, tag, set)					\
  (((tag) << (cp)->tag_shift)|((set) << (cp)->set_shift))

/* index an array of cache blocks, non-trivial due to variable length blocks */
#define CACHE_BINDEX(cp, blks, i)					\
  ((struct cache_blk_t *)(((char *)(blks)) +				\
			  (i)*(sizeof(struct cache_blk_t) +		\
			       ((cp)->balloc				\
				? (cp)->bsize*sizeof(byte_t) : 0))))

/* cache data block accessor, type parameterized */
#define __CACHE_ACCESS(type, data, bofs)				\
  (*((type *)(((char *)data) + (bofs))))

/* cache data block accessors, by type */
#define CACHE_DOUBLE(data, bofs)  __CACHE_ACCESS(double, data, bofs)
#define CACHE_FLOAT(data, bofs)	  __CACHE_ACCESS(float, data, bofs)
#define CACHE_WORD(data, bofs)	  __CACHE_ACCESS(unsigned int, data, bofs)
#define CACHE_HALF(data, bofs)	  __CACHE_ACCESS(unsigned short, data, bofs)
#define CACHE_BYTE(data, bofs)	  __CACHE_ACCESS(unsigned char, data, bofs)

/* cache block hashing macros, this macro is used to index into a cache
   set hash table (to find the correct block on N in an N-way cache), the
   cache set index function is CACHE_SET, defined above */
#define CACHE_HASH(cp, key)						\
  (((key >> 24) ^ (key >> 16) ^ (key >> 8) ^ key) & ((cp)->hsize-1))

/* copy data out of a cache block to buffer indicated by argument pointer p */
#define CACHE_BCOPY(cmd, blk, bofs, p, nbytes)	\
  if (cmd == Read)							\
    {									\
      switch (nbytes) {							\
      case 1:								\
	*((byte_t *)p) = CACHE_BYTE(&blk->data[0], bofs); break;	\
      case 2:								\
	*((half_t *)p) = CACHE_HALF(&blk->data[0], bofs); break;	\
      case 4:								\
	*((word_t *)p) = CACHE_WORD(&blk->data[0], bofs); break;	\
      default:								\
	{ /* >= 8, power of two, fits in block */			\
	  int words = nbytes >> 2;					\
	  while (words-- > 0)						\
	    {								\
	      *((word_t *)p) = CACHE_WORD(&blk->data[0], bofs);	\
	      p += 4; bofs += 4;					\
	    }\
	}\
      }\
    }\
  else /* cmd == Write */						\
    {									\
      switch (nbytes) {							\
      case 1:								\
	CACHE_BYTE(&blk->data[0], bofs) = *((byte_t *)p); break;	\
      case 2:								\
        CACHE_HALF(&blk->data[0], bofs) = *((half_t *)p); break;	\
      case 4:								\
	CACHE_WORD(&blk->data[0], bofs) = *((word_t *)p); break;	\
      default:								\
	{ /* >= 8, power of two, fits in block */			\
	  int words = nbytes >> 2;					\
	  while (words-- > 0)						\
	    {								\
	      CACHE_WORD(&blk->data[0], bofs) = *((word_t *)p);		\
	      p += 4; bofs += 4;					\
	    }\
	}\
    }\
  }

/* bound sqword_t/dfloat_t to positive int */
#define BOUND_POS(N)		((int)(MIN(MAX(0, (N)), 2147483647)))

/* unlink BLK from the hash table bucket chain in SET */
static void
unlink_htab_ent(struct cache_t *cp,		/* cache to update */
		struct cache_set_t *set,	/* set containing bkt chain */
		struct cache_blk_t *blk)	/* block to unlink */
{
  struct cache_blk_t *prev, *ent;
  int index = CACHE_HASH(cp, blk->tag);

  /* locate the block in the hash table bucket chain */
  for (prev=NULL,ent=set->hash[index];
       ent;
       prev=ent,ent=ent->hash_next)
    {
      if (ent == blk)
	break;
    }
  assert(ent);

  /* unlink the block from the hash table bucket chain */
  if (!prev)
    {
      /* head of hash bucket list */
      set->hash[index] = ent->hash_next;
    }
  else
    {
      /* middle or end of hash bucket list */
      prev->hash_next = ent->hash_next;
    }
  ent->hash_next = NULL;
}

/* insert BLK onto the head of the hash table bucket chain in SET */
static void
link_htab_ent(struct cache_t *cp,		/* cache to update */
	      struct cache_set_t *set,		/* set containing bkt chain */
	      struct cache_blk_t *blk)		/* block to insert */
{
  int index = CACHE_HASH(cp, blk->tag);

  /* insert block onto the head of the bucket chain */
  blk->hash_next = set->hash[index];
  set->hash[index] = blk;
}

/* where to insert a block onto the ordered way chain */
enum list_loc_t { Head, Tail };

/* insert BLK into the order way chain in SET at location WHERE */
static void
update_way_list(struct cache_set_t *set,	/* set contained way chain */
		struct cache_blk_t *blk,	/* block to insert */
		enum list_loc_t where)		/* insert location */
{
  /* unlink entry from the way list */
  if (!blk->way_prev && !blk->way_next)
    {
      /* only one entry in list (direct-mapped), no action */
      assert(set->way_head == blk && set->way_tail == blk);
      /* Head/Tail order already */
      return;
    }
  /* else, more than one element in the list */
  else if (!blk->way_prev)
    {
      assert(set->way_head == blk && set->way_tail != blk);
      if (where == Head)
	{
	  /* already there */
	  return;
	}
      /* else, move to tail */
      set->way_head = blk->way_next;
      blk->way_next->way_prev = NULL;
    }
  else if (!blk->way_next)
    {
      /* end of list (and not front of list) */
      assert(set->way_head != blk && set->way_tail == blk);
      if (where == Tail)
	{
	  /* already there */
	  return;
	}
      set->way_tail = blk->way_prev;
      blk->way_prev->way_next = NULL;
    }
  else
    {
      /* middle of list (and not front or end of list) */
      assert(set->way_head != blk && set->way_tail != blk);
      blk->way_prev->way_next = blk->way_next;
      blk->way_next->way_prev = blk->way_prev;
    }

  /* link BLK back into the list */
  if (where == Head)
    {
      /* link to the head of the way list */
      blk->way_next = set->way_head;
      blk->way_prev = NULL;
      set->way_head->way_prev = blk;
      set->way_head = blk;
    }
  else if (where == Tail)
    {
      /* link to the tail of the way list */
      blk->way_prev = set->way_tail;
      blk->way_next = NULL;
      set->way_tail->way_next = blk;
      set->way_tail = blk;
    }
  else
    panic("bogus WHERE designator");
}

/* create and initialize a general cache structure */
struct cache_t *			/* pointer to cache created */
cache_create(char *name,		/* name of the cache */
	     int nsets,			/* total number of sets in cache */
	     int bsize,			/* block (line) size of cache */
	     int balloc,		/* allocate data space for blocks? */
	     int usize,			/* size of user data to alloc w/blks */
	     int assoc,			/* associativity of cache */
	     enum cache_policy policy,	/* replacement policy w/in sets */
	     /* block access function, see description w/in struct cache def */
	     unsigned int (*blk_access_fn)(enum mem_cmd cmd,
					   md_addr_t baddr, int bsize,
					   struct cache_blk_t *blk,
					   tick_t now),
	     unsigned int hit_latency)	/* latency in cycles for a hit */
{
  struct cache_t *cp;
  struct cache_blk_t *blk;
  int i, j, bindex;

  /* check all cache parameters */
  if (nsets <= 0)
    fatal("cache size (in sets) `%d' must be non-zero", nsets);
  if ((nsets & (nsets-1)) != 0)
    fatal("cache size (in sets) `%d' is not a power of two", nsets);
  /* blocks must be at least one datum large, i.e., 8 bytes for SS */
  //if (bsize < 8)
  //  fatal("cache block size (in bytes) `%d' must be 8 or greater", bsize);
  if ((bsize & (bsize-1)) != 0)
    fatal("cache block size (in bytes) `%d' must be a power of two", bsize);
  if (usize < 0)
    fatal("user data size (in bytes) `%d' must be a positive value", usize);
  if (assoc <= 0)
    fatal("cache associativity `%d' must be non-zero and positive", assoc);
  if ((assoc & (assoc-1)) != 0)
    fatal("cache associativity `%d' must be a power of two", assoc);
  if (!blk_access_fn)
    fatal("must specify miss/replacement functions");

  /* allocate the cache structure */
  cp = (struct cache_t *)
    calloc(1, sizeof(struct cache_t) + (nsets-1)*sizeof(struct cache_set_t));
  if (!cp)
    fatal("out of virtual memory");

  /* initialize user parameters */
  cp->name = mystrdup(name);
  cp->nsets = nsets;
  cp->bsize = bsize;
  cp->balloc = balloc;
  cp->usize = usize;
  cp->assoc = assoc;
  cp->policy = policy;
  cp->hit_latency = hit_latency;

  /* miss/replacement functions */
  cp->blk_access_fn = blk_access_fn;

  /* compute derived parameters */
  cp->hsize = CACHE_HIGHLY_ASSOC(cp) ? (assoc >> 2) : 0;
  cp->blk_mask = bsize-1;
  cp->set_shift = log_base2(bsize);
  cp->set_mask = nsets-1;
  cp->tag_shift = cp->set_shift + log_base2(nsets);
  cp->tag_mask = (1 << (32 - cp->tag_shift))-1;
  cp->tagset_mask = ~cp->blk_mask;
  cp->bus_free = 0;

  /* print derived parameters during debug */
  debug("%s: cp->hsize     = %d", cp->name, cp->hsize);
  debug("%s: cp->blk_mask  = 0x%08x", cp->name, cp->blk_mask);
  debug("%s: cp->set_shift = %d", cp->name, cp->set_shift);
  debug("%s: cp->set_mask  = 0x%08x", cp->name, cp->set_mask);
  debug("%s: cp->tag_shift = %d", cp->name, cp->tag_shift);
  debug("%s: cp->tag_mask  = 0x%08x", cp->name, cp->tag_mask);

  /* initialize cache stats */
  cp->hits = 0;
  cp->misses = 0;
  cp->replacements = 0;
  cp->writebacks = 0;
  cp->invalidations = 0;

  /* blow away the last block accessed */
  cp->last_tagset = -1;
  cp->last_blk = NULL;

  /* allocate data blocks */
  cp->data = (byte_t *)calloc(nsets * assoc,
			      sizeof(struct cache_blk_t) +
			      (cp->balloc ? (bsize*sizeof(byte_t)) : 0));
  if (!cp->data)
    fatal("out of virtual memory");

  /* slice up the data blocks */
  for (bindex=0,i=0; i<nsets; i++)
    {
      cp->sets[i].dead_block_count = 0;
      cp->sets[i].way_head = NULL;
      cp->sets[i].way_tail = NULL;
        
        cp->sets[i].MRU = -1;
        
      /* get a hash table, if needed */
      if (cp->hsize)
	{
	  cp->sets[i].hash =
	    (struct cache_blk_t **)calloc(cp->hsize,
					  sizeof(struct cache_blk_t *));
	  if (!cp->sets[i].hash)
	    fatal("out of virtual memory");
	}
      /* NOTE: all the blocks in a set *must* be allocated contiguously,
	 otherwise, block accesses through SET->BLKS will fail (used
	 during random replacement selection) */
      cp->sets[i].blks = CACHE_BINDEX(cp, cp->data, bindex);
      
      /* link the data blocks into ordered way chain and hash table bucket
         chains, if hash table exists */
      for (j=0; j<assoc; j++)
	{
	  /* locate next cache block */
	  blk = CACHE_BINDEX(cp, cp->data, bindex);
	  bindex++;

	  /* invalidate new cache block */
	  blk->status = 0;
	  blk->tag = 0;
	  blk->ready = 0;
	  blk->user_data = (usize != 0
			    ? (byte_t *)calloc(usize, sizeof(byte_t)) : NULL);
	  blk->is_dead = 0;
	  blk->encoding = 0;
	  blk->prev_encoding = -1;
	  blk->prev_addr = -1;
	  blk->added = 0;
	  blk->prefetched = 0;

	  /* insert cache block into set hash table */
	  if (cp->hsize)
	    link_htab_ent(cp, &cp->sets[i], blk);

	  /* insert into head of way list, order is arbitrary at this point */
	  blk->way_next = cp->sets[i].way_head;
	  blk->way_prev = NULL;
	  if (cp->sets[i].way_head)
	    cp->sets[i].way_head->way_prev = blk;
	  cp->sets[i].way_head = blk;
	  if (!cp->sets[i].way_tail)
	    cp->sets[i].way_tail = blk;
	}
    }
  return cp;
}

/* parse policy */
enum cache_policy			/* replacement policy enum */
cache_char2policy(char c)		/* replacement policy as a char */
{
  switch (c) {
  case 'l': return LRU;
  case 'r': return Random;
  case 'f': return FIFO;
  default: fatal("bogus replacement policy, `%c'", c);
  }
}

/* print cache configuration */
void
cache_config(struct cache_t *cp,	/* cache instance */
	     FILE *stream)		/* output stream */
{
  fprintf(stream,
	  "cache: %s: %d sets, %d byte blocks, %d bytes user data/block\n",
	  cp->name, cp->nsets, cp->bsize, cp->usize);
  fprintf(stream,
	  "cache: %s: %d-way, `%s' replacement policy, write-back\n",
	  cp->name, cp->assoc,
	  cp->policy == LRU ? "LRU"
	  : cp->policy == Random ? "Random"
	  : cp->policy == FIFO ? "FIFO"
	  : (abort(), ""));
}

/* register cache stats */
void
cache_reg_stats(struct cache_t *cp,	/* cache instance */
		struct stat_sdb_t *sdb)	/* stats database */
{
  char buf[512], buf1[512], *name;

  /* get a name for this cache */
  if (!cp->name || !cp->name[0])
    name = "<unknown>";
  else
    name = cp->name;

  sprintf(buf, "%s.accesses", name);
  sprintf(buf1, "%s.hits + %s.misses", name, name);
  stat_reg_formula(sdb, buf, "total number of accesses", buf1, "%12.0f");
  sprintf(buf, "%s.hits", name);
  stat_reg_counter(sdb, buf, "total number of hits", &cp->hits, 0, NULL);
  sprintf(buf, "%s.misses", name);
  stat_reg_counter(sdb, buf, "total number of misses", &cp->misses, 0, NULL);
  sprintf(buf, "%s.replacements", name);
  stat_reg_counter(sdb, buf, "total number of replacements",
		 &cp->replacements, 0, NULL);
  sprintf(buf, "%s.writebacks", name);
  stat_reg_counter(sdb, buf, "total number of writebacks",
		 &cp->writebacks, 0, NULL);
  sprintf(buf, "%s.invalidations", name);
  stat_reg_counter(sdb, buf, "total number of invalidations",
		 &cp->invalidations, 0, NULL);
  sprintf(buf, "%s.miss_rate", name);
  sprintf(buf1, "%s.misses / %s.accesses", name, name);
  stat_reg_formula(sdb, buf, "miss rate (i.e., misses/ref)", buf1, NULL);
  sprintf(buf, "%s.repl_rate", name);
  sprintf(buf1, "%s.replacements / %s.accesses", name, name);
  stat_reg_formula(sdb, buf, "replacement rate (i.e., repls/ref)", buf1, NULL);
  sprintf(buf, "%s.wb_rate", name);
  sprintf(buf1, "%s.writebacks / %s.accesses", name, name);
  stat_reg_formula(sdb, buf, "writeback rate (i.e., wrbks/ref)", buf1, NULL);
  sprintf(buf, "%s.inv_rate", name);
  sprintf(buf1, "%s.invalidations / %s.accesses", name, name);
  stat_reg_formula(sdb, buf, "invalidation rate (i.e., invs/ref)", buf1, NULL);
}

/* print cache stats */
void
cache_stats(struct cache_t *cp,		/* cache instance */
	    FILE *stream)		/* output stream */
{
  double sum = (double)(cp->hits + cp->misses);

  fprintf(stream,
	  "cache: %s: %.0f hits %.0f misses %.0f repls %.0f invalidations\n",
	  cp->name, (double)cp->hits, (double)cp->misses,
	  (double)cp->replacements, (double)cp->invalidations);
  fprintf(stream,
	  "cache: %s: miss rate=%f  repl rate=%f  invalidation rate=%f\n",
	  cp->name,
	  (double)cp->misses/sum, (double)(double)cp->replacements/sum,
	  (double)cp->invalidations/sum);
}

/* access a cache, perform a CMD operation on cache CP at address ADDR,
   places NBYTES of data at *P, returns latency of operation if initiated
   at NOW, places pointer to block user data in *UDATA, *P is untouched if
   cache blocks are not allocated (!CP->BALLOC), UDATA should be NULL if no
   user data is attached to blocks */
unsigned int				/* latency of access in cycles */
cache_access(struct cache_t *cp,	/* cache to access */
	     enum mem_cmd cmd,		/* access type, Read or Write */
	     md_addr_t addr,		/* address of access */
	     void *vp,			/* ptr to buffer for input/output */
	     int nbytes,		/* number of bytes to access */
	     tick_t now,		/* time of access */
	     byte_t **udata,		/* for return of user data ptr */
	     md_addr_t *repl_addr)	/* for address of replaced block */
{
  byte_t *p = vp;
  md_addr_t tag = CACHE_TAG(cp, addr);
  md_addr_t set = CACHE_SET(cp, addr);
  md_addr_t bofs = CACHE_BLK(cp, addr);
  struct cache_blk_t *blk, *repl;
  int lat = 0;
  repl = NULL;

  /* default replacement address */
  if (repl_addr)
    *repl_addr = -1;

  /* check alignments */
  if ((nbytes & (nbytes-1)) != 0 || (addr & (nbytes-1)) != 0)
    fatal("cache: access error: bad size or alignment, addr 0x%08x", addr);

  /* access must fit in cache block */
  /* FIXME:
     ((addr + (nbytes - 1)) > ((addr & ~cp->blk_mask) + (cp->bsize - 1))) */
  if ((addr + nbytes) > ((addr & ~cp->blk_mask) + cp->bsize))
    fatal("cache: access error: access spans block, addr 0x%08x", addr);


  /* permissions are checked on cache misses */
  /* check for a fast hit: access to same block */
  if (CACHE_TAGSET(cp, addr) == cp->last_tagset)
    {
      /* hit in the same block */
      blk = cp->last_blk;
      goto cache_fast_hit;
    }
    
  if (cp->hsize)
    {
      /* higly-associativity cache, access through the per-set hash tables */
      int hindex = CACHE_HASH(cp, tag);

      for (blk=cp->sets[set].hash[hindex];
	   blk;
	   blk=blk->hash_next)
	{
	  if (blk->tag == tag && (blk->status & CACHE_BLK_VALID))
	    goto cache_hit;
	}
    }
  else
    {
      /* low-associativity cache, linear search the way list */
      for (blk=cp->sets[set].way_head;
	   blk;
	   blk=blk->way_next)
	{
	  if (blk->tag == tag && (blk->status & CACHE_BLK_VALID))
	    goto cache_hit;
	}
    }

  /* cache block not found */

  /* **MISS** */
  cp->misses++;

/* JLinge Edit: Updated replacement policy based on dead blocks

	Add a boolean to each block saying if it has been predicted dead or not.
	Add a counter to the set to count the number of dead blocks.
	if set counter > 0 then search all the blocks and take the first predicted dead.
	decrement the counter and update the block
 */

  //Set contains a dead block
  if((cp->sets[set].way_tail->status & CACHE_BLK_VALID)//Only for LRU
  && cp->sets[set].dead_block_count > 0)	
  {
	int dead_index = myrand() % cp->sets[set].dead_block_count;
	//fprintf(stderr, "%x set[%d](%d)\n", addr, set, cp->sets[set].dead_block_count);
	--cp->sets[set].dead_block_count;
	
	int curr = 0;
	if (cp->hsize)
	    {
	      /* higly-associativity cache, access through the per-set hash tables */
	      int hindex = CACHE_HASH(cp, tag);

	      for (blk=cp->sets[set].hash[hindex];
		   blk;
		   blk=blk->hash_next)
		{
		  if (blk->is_dead == 1 && (blk->status & CACHE_BLK_VALID))
		  {
			if(curr == dead_index)
				break;
			++curr;
		  }
		}
	    }
	  else
	    {
		//Take the most LRU dead block
		dead_index = cp->sets[set].dead_block_count;

	      /* low-associativity cache, linear search the way list */
	      for (blk=cp->sets[set].way_head;
		   blk;
		   blk=blk->way_next)
		{
		  if (blk->is_dead == 1 && (blk->status & CACHE_BLK_VALID))
		  {
			if(curr == dead_index)
				break;
			++curr;
		  }
		}
	    }	
	
	repl = blk;
	repl->is_dead = 0;
	update_way_list(&cp->sets[set], repl, Head);
	//fprintf(stderr, "DB Found: %x\n", CACHE_MK_BADDR(cp, repl->tag, set));
  }
  //No dead block within this set, use normal replacement
  else
  {
	  /* select the appropriate block to replace, and re-link this entry to
	     the appropriate place in the way list */
	  switch (cp->policy) {
	  case LRU:
	  case FIFO:
	    repl = cp->sets[set].way_tail;
	    update_way_list(&cp->sets[set], repl, Head);
	    break;
	  case Random:
	    {
	      int bindex = myrand() & (cp->assoc - 1);
	      repl = CACHE_BINDEX(cp, cp->sets[set].blks, bindex);
	    }
	    break;
	  default:
	    panic("bogus replacement policy");
	  }
  }

  /* remove this block from the hash bucket chain, if hash exists */
  if (cp->hsize)
    unlink_htab_ent(cp, &cp->sets[set], repl);

  /* blow away the last block to hit */
  cp->last_tagset = -1;
  cp->last_blk = NULL;

  /* write back replaced block data */
  if (repl->status & CACHE_BLK_VALID)
    {
      cp->replacements++;

      if (repl_addr)
	*repl_addr = CACHE_MK_BADDR(cp, repl->tag, set);
 
      /* don't replace the block until outstanding misses are satisfied */
      lat += BOUND_POS(repl->ready - now);
 
      /* stall until the bus to next level of memory is available */
      lat += BOUND_POS(cp->bus_free - (now + lat));
 
      /* track bus resource usage */
      cp->bus_free = MAX(cp->bus_free, (now + lat)) + 1;

      if (repl->status & CACHE_BLK_DIRTY)
	{
	  /* write back the cache block */
	  cp->writebacks++;
	  lat += cp->blk_access_fn(Write,
				   CACHE_MK_BADDR(cp, repl->tag, set),
				   cp->bsize, repl, now+lat);
	}

	if(strcmp(cp->name, "dl1") == 0)
	{
		if(repl->prefetched == 1 && repl->encoding == history_table_encode(repl->prev_addr, 0))
		{
			//fprintf(stderr, "bad prefetch\n");
			//*
			dead_block_table_remove(cp->dead_block_table,
				repl->prev_addr,
				repl->prev_encoding,
				CACHE_MK_BADDR(cp, repl->tag, set));
			//*/
			repl->added = 1;
		}
		else
		{
			repl->added = 0;
			//fprintf(stderr, "good prefetch?\n");
		}
	}

	repl->prev_addr = CACHE_MK_BADDR(cp, repl->tag, set);
	repl->prev_encoding = repl->encoding;

	//Save the previous address as the start of the new encoding
	repl->encoding = history_table_encode(repl->prev_addr, 0);
	
	//if(strcmp(cp->name, "dl1") == 0)
	//fprintf(stderr, "%x replaced %x (%x)\n", addr, repl->prev_addr, repl->prev_encoding);
    }
//Block was not valid, keep previous as invalid
    else
    {
	repl->prev_addr = -1;
	repl->prev_encoding = -1;

	//Encoding starts blank since replacing an invalid block
  	repl->encoding = -1;
	repl->added = 0;
    }	

  repl->prefetched = now == 0;

  /* update block tags */
  repl->tag = tag;
  repl->status = CACHE_BLK_VALID;	/* dirty bit set on update */

  /* read data block */
  lat += cp->blk_access_fn(Read, CACHE_BADDR(cp, addr), cp->bsize,
			   repl, now+lat);

  /* copy data out of cache block */
  if (cp->balloc)
    {
      CACHE_BCOPY(cmd, repl, bofs, p, nbytes);
    }

  /* update dirty status */
  if (cmd == Write)
    repl->status |= CACHE_BLK_DIRTY;

  /* get user block data, if requested and it exists */
  if (udata)
    *udata = repl->user_data;

  /* update block status */
  repl->ready = now+lat;

  /* link this entry back into the hash table */
  if (cp->hsize)
    link_htab_ent(cp, &cp->sets[set], repl);

  /* return latency of the operation */
  return lat;


 cache_hit: /* slow hit handler */
 
	/*if(blk->is_dead)
	{
		--cp->sets[set].dead_block_count;
		blk->is_dead = 0;
		fprintf(stderr, "Not dead yet");
		dead_block_table_remove(cp->dead_block_table,
				blk->prev_addr,
				blk->prev_encoding,
				-1);
	}*/

  /* **HIT** */
  cp->hits++;

  /* copy data out of cache block, if block exists */
  if (cp->balloc)
    {
      CACHE_BCOPY(cmd, blk, bofs, p, nbytes);
    }

  /* update dirty status */
  if (cmd == Write)
    blk->status |= CACHE_BLK_DIRTY;

  /* if LRU replacement and this is not the first element of list, reorder */
  if (blk->way_prev && cp->policy == LRU)
    {
      /* move this block to head of the way (MRU) list */
      update_way_list(&cp->sets[set], blk, Head);
    }

  /* tag is unchanged, so hash links (if they exist) are still valid */

  /* record the last block to hit */
  cp->last_tagset = CACHE_TAGSET(cp, addr);
  cp->last_blk = blk;

  /* get user block data, if requested and it exists */
  if (udata)
    *udata = blk->user_data;

  /* return first cycle data is available to access */
  return (int) MAX(cp->hit_latency, (blk->ready - now));

 cache_fast_hit: /* fast hit handler */

  /* **FAST HIT** */
  cp->hits++;

  /* copy data out of cache block, if block exists */
  if (cp->balloc)
    {
      CACHE_BCOPY(cmd, blk, bofs, p, nbytes);
    }

  /* update dirty status */
  if (cmd == Write)
    blk->status |= CACHE_BLK_DIRTY;

  /* this block hit last, no change in the way list */

  /* tag is unchanged, so hash links (if they exist) are still valid */

  /* get user block data, if requested and it exists */
  if (udata)
    *udata = blk->user_data;

  /* record the last block to hit */
  cp->last_tagset = CACHE_TAGSET(cp, addr);
  cp->last_blk = blk;

  /* return first cycle data is available to access */
  return (int) MAX(cp->hit_latency, (blk->ready - now));
}

/* return non-zero if block containing address ADDR is contained in cache
   CP, this interface is used primarily for debugging and asserting cache
   invariants */
int					/* non-zero if access would hit */
cache_probe(struct cache_t *cp,		/* cache instance to probe */
	    md_addr_t addr)		/* address of block to probe */
{
  md_addr_t tag = CACHE_TAG(cp, addr);
  md_addr_t set = CACHE_SET(cp, addr);
  struct cache_blk_t *blk;

  /* permissions are checked on cache misses */

  if (cp->hsize)
  {
    /* higly-associativity cache, access through the per-set hash tables */
    int hindex = CACHE_HASH(cp, tag);
    
    for (blk=cp->sets[set].hash[hindex];
	 blk;
	 blk=blk->hash_next)
    {	
      if (blk->tag == tag && (blk->status & CACHE_BLK_VALID))
	  return TRUE;
    }
  }
  else
  {
    /* low-associativity cache, linear search the way list */
    for (blk=cp->sets[set].way_head;
	 blk;
	 blk=blk->way_next)
    {
      if (blk->tag == tag && (blk->status & CACHE_BLK_VALID))
	  return TRUE;
    }
  }
  
  /* cache block not found */
  return FALSE;
}

/* flush the entire cache, returns latency of the operation */
unsigned int				/* latency of the flush operation */
cache_flush(struct cache_t *cp,		/* cache instance to flush */
	    tick_t now)			/* time of cache flush */
{
  int i, lat = cp->hit_latency; /* min latency to probe cache */
  struct cache_blk_t *blk;

  /* blow away the last block to hit */
  cp->last_tagset = 0;
  cp->last_blk = NULL;

  /* no way list updates required because all blocks are being invalidated */
  for (i=0; i<cp->nsets; i++)
    {
      for (blk=cp->sets[i].way_head; blk; blk=blk->way_next)
	{
	  if (blk->status & CACHE_BLK_VALID)
	    {
	      cp->invalidations++;
	      blk->status &= ~CACHE_BLK_VALID;

	      if (blk->status & CACHE_BLK_DIRTY)
		{
		  /* write back the invalidated block */
          	  cp->writebacks++;
		  lat += cp->blk_access_fn(Write,
					   CACHE_MK_BADDR(cp, blk->tag, i),
					   cp->bsize, blk, now+lat);
		}
	    }
	}
    }

  /* return latency of the flush operation */
  return lat;
}

/* flush the block containing ADDR from the cache CP, returns the latency of
   the block flush operation */
unsigned int				/* latency of flush operation */
cache_flush_addr(struct cache_t *cp,	/* cache instance to flush */
		 md_addr_t addr,	/* address of block to flush */
		 tick_t now)		/* time of cache flush */
{
  md_addr_t tag = CACHE_TAG(cp, addr);
  md_addr_t set = CACHE_SET(cp, addr);
  struct cache_blk_t *blk;
  int lat = cp->hit_latency; /* min latency to probe cache */

  if (cp->hsize)
    {
      /* higly-associativity cache, access through the per-set hash tables */
      int hindex = CACHE_HASH(cp, tag);

      for (blk=cp->sets[set].hash[hindex];
	   blk;
	   blk=blk->hash_next)
	{
	  if (blk->tag == tag && (blk->status & CACHE_BLK_VALID))
	    break;
	}
    }
  else
    {
      /* low-associativity cache, linear search the way list */
      for (blk=cp->sets[set].way_head;
	   blk;
	   blk=blk->way_next)
	{
	  if (blk->tag == tag && (blk->status & CACHE_BLK_VALID))
	    break;
	}
    }

  if (blk)
    {
      cp->invalidations++;
      blk->status &= ~CACHE_BLK_VALID;

      /* blow away the last block to hit */
      cp->last_tagset = 0;
      cp->last_blk = NULL;

      if (blk->status & CACHE_BLK_DIRTY)
	{
	  /* write back the invalidated block */
          cp->writebacks++;
	  lat += cp->blk_access_fn(Write,
				   CACHE_MK_BADDR(cp, blk->tag, set),
				   cp->bsize, blk, now+lat);
	}
      /* move this block to tail of the way (LRU) list */
      update_way_list(&cp->sets[set], blk, Tail);
    }

  /* return latency of the operation */
  return lat;
}


//JLinge edit:

unsigned int				/* latency of access in cycles */
cache_access_and_encode
	     (struct cache_t *cp,	/* cache to access */
	     enum mem_cmd cmd,		/* access type, Read or Write */
	     md_addr_t addr,		/* address of access */
	     void *vp,			/* ptr to buffer for input/output */
	     int nbytes,		/* number of bytes to access */
	     tick_t now,		/* time of access */
	     byte_t **udata,		/* for return of user data ptr */
	     md_addr_t *repl_addr,	/* for address of replaced block */
	     md_addr_t PC,
	     enum dead_block_predictor dead_block_predictor,
	     struct cache_t *dead_block_table)
{
	unsigned int lat = cache_access(cp, cmd, addr, vp, nbytes, now, udata, repl_addr);
	
	md_addr_t blk_addr = ((addr) & ~(cp)->blk_mask);
	word_t encoding = encode_block_trace(cp, 
				blk_addr, 
				PC);
//*
	if(dead_block_predictor == RefTrace || dead_block_predictor == BurstTrace) 
	{
		word_t repl_addr = get_replaced_block_addr(cp, 
					blk_addr);
		word_t repl_encode = get_replaced_block_trace(cp, 
					blk_addr);

		if(repl_addr != -1)
		{	
			if(repl_encode == -1)
				fprintf(stderr, "error?");
			//fprintf(stderr, "adding %x %x %x\n", repl_addr, repl_encode, blk_addr);
			dead_block_table_add(dead_block_table,
						repl_addr,
						repl_encode,
						blk_addr);
		}
	}//*/

	if(dead_block_predictor == RefTrace)
	{
		reference_trace_prediction(cp, 
			dead_block_table, 
			blk_addr,
			PC);
		//fprintf(stderr, "%x %x\n", blk_addr, rs->PC);
	}
	else if (dead_block_predictor == BurstTrace)
	{
		burst_trace_prediction(cp, 
			dead_block_table, 
			blk_addr,
			PC);
	}

	return lat;
}

struct cache_blk_t *
get_block_at_addr(struct cache_t *cp,
		  md_addr_t addr)
{
  md_addr_t tag = CACHE_TAG(cp, addr);
  md_addr_t set = CACHE_SET(cp, addr);
  struct cache_blk_t *blk;

  /* permissions are checked on cache misses */
  /* check for a fast hit: access to same block */
  if (CACHE_TAGSET(cp, addr) == cp->last_tagset)
    {
      /* hit in the same block */
      blk = cp->last_blk;
      return blk;
    }
    
  if (cp->hsize)
    {
      /* higly-associativity cache, access through the per-set hash tables */
      int hindex = CACHE_HASH(cp, tag);

      for (blk=cp->sets[set].hash[hindex];
	   blk;
	   blk=blk->hash_next)
	{
	  if (blk->tag == tag && (blk->status & CACHE_BLK_VALID))
	   return blk;
	}
    }
  else
    {
      /* low-associativity cache, linear search the way list */
      for (blk=cp->sets[set].way_head;
	   blk;
	   blk=blk->way_next)
	{
	  if (blk->tag == tag && (blk->status & CACHE_BLK_VALID))
	    return blk;
	}
    }
	//fprintf(stderr, "No Block\n");
  return NULL;
}

word_t history_table_encode(md_addr_t pc, word_t encoding)
{
	if(encoding == -1)
		encoding = 0;
	//fprintf(stderr, "PC: %0x, prev: %0x, now: ", pc, *encoding);
	encoding = encoding + (pc >> 2);

	encoding = encoding & ((1 << ENCODING_WIDTH) -1);
	return encoding;
	//fprintf(stderr, "%0x\n", *encoding);
}

word_t
encode_block_trace(struct cache_t *cp,
		   md_addr_t addr,
		   md_addr_t pc)
{
	struct cache_blk_t *blk;

	blk = get_block_at_addr(cp, addr);

	if(blk == NULL)
	{
		//fprintf(stderr, "Block %x not in cache\n", addr);
		return -1;
	}

	//fprintf(stderr, " (%x -> ", blk->encoding);
	blk->encoding = history_table_encode(pc, blk->encoding);
	//fprintf(stderr, "%x) ", blk->encoding);
	return blk->encoding;
}

word_t
get_block_trace(struct cache_t *cp,
		   md_addr_t addr)
{
	struct cache_blk_t *blk;

	blk = get_block_at_addr(cp, addr);

	if(blk == NULL)
	{
		md_addr_t set = CACHE_SET(cp, addr);
		md_addr_t tag = CACHE_TAG(cp, addr);
  		for (blk=cp->sets[set].way_head;
		   blk;
		   blk=blk->way_next)
		{
		  if (CACHE_TAG(cp, blk->prev_addr) == tag)
		    return blk->prev_encoding;
		}
		//fprintf(stderr, "Block %x not in cache\n", addr);
		return -1;
	}

	return blk->encoding;
}

word_t
get_replaced_block_trace(struct cache_t *cp,
		   	md_addr_t addr)
{
	struct cache_blk_t *blk;

	blk = get_block_at_addr(cp, addr);

	if(blk == NULL)
	{
		return -1;
	}

	return blk->prev_encoding;
}

word_t
get_replaced_block_addr(struct cache_t *cp,
		   	md_addr_t addr)
{
	struct cache_blk_t *blk;

	blk = get_block_at_addr(cp, addr);

	if(blk == NULL)
	{
		//fprintf(stderr, "Block %x not in cache\n", addr);
		return -1;
	}


	if(blk->added == 1)
		return -1;
	blk->added = 1;

	//if(blk->prev_encoding == -1)
	//	fprintf(stderr, "No prev Blk\n");
	
	return blk->prev_addr;
}

int
mark_block_as_dead(struct cache_t *cp,
		   md_addr_t addr)
{
  struct cache_blk_t *blk;

  blk = get_block_at_addr(cp, addr);

  if(blk == NULL)
  {
	//fprintf(stderr, "Block %x not in cache\n", addr);
	return 0;
  }

  if(blk->is_dead)
	return 0;

  md_addr_t set = CACHE_SET(cp, addr);
  //fprintf(stderr, "Dead: %x set[%d](%d)\n", addr, set, cp->sets[set].dead_block_count);

  ++cp->sets[set].dead_block_count;
  blk->is_dead = 1;

  return 1;
}

int numBytes = 1;
int encoding_shift = 0;//(32 - ENCODING_WIDTH);

word_t
make_dead_block_table_address(md_addr_t addr,
				word_t encoding)
{
	word_t DBTAddr;
	//return (addr ^ (encoding << encoding_shift)) & (~(numBytes-1));

	//word_t originalEncoding = encoding;
	encoding = history_table_encode(addr, encoding);
	encoding = history_table_encode(~addr >> 16, encoding);
	
	DBTAddr = (addr ^ (encoding << encoding_shift)) & (~(numBytes-1));
	//DBTAddr = (addr ^ encoding) << 4;
	//DBTAddr = (encoding << encoding_shift);

	//word_t add = (addr << 16) + (((addr >> 15) & (~3)) << 15);
	word_t left = (addr >> 16);
	word_t right = (~addr & ((1 << 16)-1));
	word_t add = left + right;
	//add = (add) << 16;
	//fprintf(stderr, "%x %x %x %x\n", addr, left, right, add);
	
	//DBTAddr ^= right << 4;
	add = (add << numBytes) ^ (add << 16);
	//add ^= encoding << (32 - ENCODING_WIDTH);

	DBTAddr = (add ^ DBTAddr) & (~(numBytes-1));
	return DBTAddr;
}

int
dead_block_table_check(struct cache_t *dead_block_table,
			md_addr_t addr,
			word_t encoding)
{
	word_t DBTAddr = make_dead_block_table_address(addr, encoding);

	int probe = cache_probe(dead_block_table, DBTAddr);
	
	//Not in the cache
	if(!probe)
		return 0;

	//fprintf(stderr, "Dead %x\n", addr);

	byte_t * data;
	
	//Read table
	cache_access(dead_block_table, Read,
		    DBTAddr, NULL, 1,
		    0, &data, NULL);
	
	if(*((word_t*)data) == 0)
		return 0;

	struct DBT_entry_link * link = (struct DBT_entry_link *)data;
	struct DBT_entry * entry = get_DBT_entry(link, addr, encoding, 1);

	if(entry == NULL)
		return 0;

	//fprintf(stderr, "%x ", entry->count);

	if(entry->entries[0].count < DEAD_BLOCK_TABLE_MAX_SATURATION)
		return 0;

/*
	fprintf(stderr, "( ");
	int i;
	for(i = 0; i < NUM_DBT_ENTRIES_ADDR && entry->entries[i].count != -1; ++i)
	{
		fprintf(stderr, "%d ", entry->entries[i].count);
	}
	fprintf(stderr, ") ");
*/
	if(entry->entries[0].pfch_addr == -1)
		return 0;

	return entry->entries[0].pfch_addr;
}

void
dead_block_table_add(struct cache_t *dead_block_table,
			md_addr_t addr,
			word_t encoding,
			md_addr_t prefetch_addr)
{
	//fprintf(stderr, "Adding %x %x %x\n", addr, encoding, prefetch_addr);
	word_t DBTAddr = make_dead_block_table_address(addr, encoding);
	
	//int probe = cache_probe(dead_block_table, DBTAddr);
	
	byte_t * data;

	//Read table
	cache_access(dead_block_table, Read,
		    DBTAddr, NULL, 1,
		    0, &data, NULL);


	if(*((word_t*)data) == 0)
	{
		struct DBT_entry_link * link = create_DBT_entry_link();

		//fprintf(stderr, "%x ", *link);
		*((struct DBT_entry_link *)data) = *link;
		//fprintf(stderr, "%x C\n", *((struct DBT_entry_link *)data));
	}

	struct DBT_entry_link * link = (struct DBT_entry_link *)data;
	//fprintf(stderr, "%x ", *link);
	//fprintf(stderr, "%x %d\n", *((struct DBT_entry_link *)data), probe);


	struct DBT_entry * entry = get_DBT_entry(link, addr, encoding, 0);

	
	if(entry == NULL)
		fatal("Null entry?");

	int i;
	for(i = 0; i < NUM_DBT_ENTRIES_ADDR; ++i)
	{
		if(entry->entries[i].pfch_addr == prefetch_addr)
		{
			//if(entry->entries[i].count < DEAD_BLOCK_TABLE_MAX_SATURATION)
				++entry->entries[i].count;
			
			break;
		}
		else if (entry->entries[i].pfch_addr == -1)
		{
			entry->entries[i].pfch_addr = prefetch_addr;
			entry->entries[i].count = 0;
			break;
		}
	}
	
	//All entries taken
	if(i == NUM_DBT_ENTRIES_ADDR)
	{
		--i;
		entry->entries[i].pfch_addr = prefetch_addr;
		entry->entries[i].count = 0;
		//fprintf(stderr, " new ");
	}


	//Move up
	int j;
	for(j = i-1; j >= 0; --j)
	{
		if(entry->entries[i].count >= entry->entries[j].count)
		{
			word_t tempCount = entry->entries[i].count;
			entry->entries[i].count = entry->entries[j].count;
			entry->entries[j].count = tempCount;

			md_addr_t tempAddr = entry->entries[i].pfch_addr;
			entry->entries[i].pfch_addr = entry->entries[j].pfch_addr;
			entry->entries[j].pfch_addr = tempAddr;
			i = j;
		}
	}
	

/*
	if(entry->pfch_addr != prefetch_addr)
	{	
		if(entry->count > 0)
			fprintf(stderr, "new prefetch %d\n", entry->count);
		entry->pfch_addr = prefetch_addr;
		entry->count = 0;
	}
//*/

/*
	if(entry->count > 0)
	{
		fprintf(stderr, "Addr %x En: %x pfc: %x cnt: %d dbaddr: %x\n", addr, encoding, prefetch_addr, entry->count, DBTAddr);
	}//*/
}

void
dead_block_table_remove(struct cache_t *dead_block_table,
			md_addr_t addr,
			word_t encoding,
			md_addr_t prefetch_addr)
{
	//fprintf(stderr, "Removing %x %x %x\n", addr, encoding, prefetch_addr);
	word_t DBTAddr = make_dead_block_table_address(addr, encoding);
	
	byte_t * data;
	//Read table
	cache_access(dead_block_table, Read,
		    DBTAddr, NULL, 1,
		    0, &data, NULL);
	
	if(*((word_t*)data) == 0)
	{
		return;
		//fatal("removing from nothing?");
	}

	struct DBT_entry_link * link = (struct DBT_entry_link *)data;
	
	struct DBT_entry * entry = get_DBT_entry(link, addr, encoding, 1);

	if(entry == NULL)
		return;
		//fatal("Null entry?");
	int i;
	for(i = 0; i < NUM_DBT_ENTRIES_ADDR; ++i)
	{
		if((prefetch_addr == -1) ^ (entry->entries[i].pfch_addr == prefetch_addr))
		{
			entry->entries[i].pfch_addr = -1;
			entry->entries[i].count = -1;
/*
			--entry->entries[i].count;
			
			if(entry->entries[i].count == -1)
				entry->entries[i].pfch_addr = -1;*/
			
			if(prefetch_addr != -1)
				break;
		}
	}

	//Move down
	int j;
	for(j = i+1; j < NUM_DBT_ENTRIES_ADDR; ++j)
	{
		if(entry->entries[i].count < entry->entries[j].count)
		{
			word_t tempCount = entry->entries[i].count;
			entry->entries[i].count = entry->entries[j].count;
			entry->entries[j].count = tempCount;

			md_addr_t tempAddr = entry->entries[i].pfch_addr;
			entry->entries[i].pfch_addr = entry->entries[j].pfch_addr;
			entry->entries[j].pfch_addr = tempAddr;
			i = j;
		}
	}
}

void
reference_trace_prediction(struct cache_t * cache_dl1,
				struct cache_t * dead_block_table,
				md_addr_t addr,
				md_addr_t PC)
{
	md_addr_t blk_addr = (addr & ~(cache_dl1)->blk_mask);

	//Get the encoding for this address.
	word_t encoding = get_block_trace(cache_dl1, 
				blk_addr);
	
	//Encoding is valid and block is still in the cache
	if(encoding != -1)
	{
		md_addr_t prefetch_addr = dead_block_table_check(
						dead_block_table,
						blk_addr,
						encoding);
		//Valid address to prefetch
		if(prefetch_addr)
		{
			int marked = mark_block_as_dead(cache_dl1, 
						blk_addr);
			//return;
			//Block was successfully marked as dead.
			//Replace marked block with prefetch data.
			if(marked)	
			{
				//fprintf(stderr, "Marked %x \n", blk_addr);
				cache_access(cache_dl1, Read, prefetch_addr,
					     NULL, 4, 0, NULL, NULL);
			}
			else
			{
				//fprintf(stderr, "could not mark %x \n", blk_addr);
			}
			
		}
	}
	else
	{
		fprintf(stderr, "%x no encoding\n", blk_addr);
	}	

}

void
burst_trace_prediction(struct cache_t * cache_dl1,
				struct cache_t * dead_block_table,
				md_addr_t addr,
				md_addr_t PC)
{
	md_addr_t tag = CACHE_TAG(cache_dl1, addr);
	md_addr_t set = CACHE_SET(cache_dl1, addr);

	if(cache_dl1->sets[set].MRU == tag)
		return;

	md_addr_t prev_MRU = cache_dl1->sets[set].MRU;
	cache_dl1->sets[set].MRU = tag;

	if(prev_MRU == -1)
		return;

	md_addr_t blk_addr = CACHE_MK_BADDR(cache_dl1, prev_MRU, set);

	//Get the encoding for this address.
	word_t encoding = get_block_trace(cache_dl1, 
				blk_addr);

	//Encoding is valid and block is still in the cache
	if(encoding != -1)
	{
		md_addr_t prefetch_addr = dead_block_table_check(
				dead_block_table,
				blk_addr,
				encoding);

		//Valid address to prefetch
		if(prefetch_addr)
		{
		    int marked = mark_block_as_dead(cache_dl1,
						    blk_addr);
		    
		    //Block was successfully marked as dead.
		    //Replace marked block with prefetch data.
		    if(marked)	
		    {
			cache_access(cache_dl1, Read, prefetch_addr,
				     NULL, 4, 0, NULL, NULL);
		    }
		}
	}
	else
	{
		fprintf(stderr, "%x no encoding\n", blk_addr);
	}
}







struct DBT_entry_link *
create_DBT_entry_link()
{
	struct DBT_entry_link * link = (struct DBT_entry_link *)calloc(1, sizeof(struct DBT_entry_link *));

	int i;
	struct DBT_entry * prev = NULL;
	for(i = 0; i < NUM_DBT_ENTRIES; ++i)
	{
		struct DBT_entry * curr = (struct DBT_entry *)calloc(1, sizeof(struct DBT_entry));
		if(prev == NULL)
		{
			link->head = curr;
		}
		else
		{
			prev->next = curr;
			curr->prev = prev;
		}
		prev = curr;
	}
	link->tail = prev;

/*
	fprintf(stderr, " %x %x:\n", link->head, link->tail);

	struct DBT_entry * curr;
	for(curr = link->head, i = 0;
		curr && i < NUM_DBT_ENTRIES; 
		curr = curr->next, ++i)
	{
		fprintf(stderr, "%x %x %x\n", curr->prev, curr, curr->next);
	}
*/
	

	return link;
}


/* insert BLK into the order way chain in SET at location WHERE */
static void
update_DBT_linked_list(struct DBT_entry_link * link,	/* set contained way chain */
		struct DBT_entry * entry,	/* block to insert */
		enum list_loc_t  where)		/* insert location */
{
  /* unlink entry from the way list */
  if (!entry->prev && !entry->next)
    {
      /* only one entry in list (direct-mapped), no action */
      assert(link->head == entry && link->tail == entry);
      /* Head/Tail order already */
      return;
    }
  /* else, more than one element in the list */
  else if (!entry->prev)
    {
      assert(link->head == entry && link->tail != entry);
      if (where == Head)
	{
	  /* already there */
	  return;
	}
      /* else, move to tail */
      link->head = entry->next;
      entry->next->prev = NULL;
    }
  else if (!entry->next)
    {
      /* end of list (and not front of list) */
      assert(link->head != entry && link->tail == entry);
      if (where == Tail)
	{
	  /* already there */
	  return;
	}
      link->tail = entry->prev;
      entry->prev->next = NULL;
    }
  else
    {
      /* middle of list (and not front or end of list) */
      assert(link->head != entry && link->tail != entry);
      entry->prev->next = entry->next;
      entry->next->prev = entry->prev;
    }

  /* link BLK back into the list */
  if (where == Head)
    {
      /* link to the head of the way list */
      entry->next = link->head;
      entry->prev = NULL;
      link->head->prev = entry;
      link->head = entry;
    }
  else if (where == Tail)
    {
      /* link to the tail of the way list */
      entry->prev = link->tail;
      entry->next = NULL;
      link->tail->next = entry;
      link->tail = entry;
    }
  else
    panic("bogus WHERE designator");
}

void
DBT_entry_initialize(struct DBT_entry * entry,
		md_addr_t addr,
		word_t encoding)
{
	entry->valid = 1;
	entry->addr = addr;
	entry->encoding = encoding;

	int i;
	for(i = 0; i < NUM_DBT_ENTRIES_ADDR; ++i)
	{
		entry->entries[i].pfch_addr = -1;
		entry->entries[i].count = -1;
	}
/*
	entry->pfch_addr1 = -1;
	entry->count1 = -1;

	entry->pfch_addr2 = -1;
	entry->count2 = -1;
*/
}

struct DBT_entry *
get_DBT_entry(struct DBT_entry_link * link,
		md_addr_t addr,
		word_t encoding,
		int search_only)
{
	struct DBT_entry * curr;
	int i;
	for(curr = link->head, i = 0;
		curr && i < NUM_DBT_ENTRIES; 
		curr = curr->next, ++i)
	{
		if(curr->addr == addr && curr->encoding == encoding)
		{
			update_DBT_linked_list(link, curr, Head);
	
			//if(!search_only && curr->count < DEAD_BLOCK_TABLE_MAX_SATURATION)
			//	++curr->count;
			return curr;
		}
		else if(!search_only && !curr->valid)
		{
			update_DBT_linked_list(link, curr, Head);
			DBT_entry_initialize(curr, addr, encoding);
			return curr;
		}
	}

	if(search_only)
		return NULL;

	//fprintf(stderr, "End");

	//Nothing found, take from the end.
	curr = link->tail;
	update_DBT_linked_list(link, curr, Head);
	DBT_entry_initialize(curr, addr, encoding);
	return curr;
}











