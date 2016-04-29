extern int      printf ();
extern int      scanf ();

int getUserOption(void);
void doDeposit(float *currentBalance);
void doWithdraw(float *currentBalance);
void doQuery(float currrentBalance, float minBalance);
float doInterest(float minBalance,float intRate);
void doStatement(int creditTx, int debitTx, float curentBalance, 
                 float minBalance, float interestAmount);

int main() {
    float minBalance, currentBalance, interestAmount;
    int option, creditTx, debitTx;
    
    currentBalance = minBalance = 2000;
    option = creditTx = debitTx = 0;
    
    do {
        option = getUserOption();
        switch (option) {
           case 1: doDeposit(&currentBalance);
                   creditTx++;
                   break;
           case 2: doWithdraw(&currentBalance);
                   debitTx++;
                   if(currentBalance < minBalance)
                      minBalance = currentBalance;
                   break;
           case 3: doQuery(currentBalance, minBalance);
                   break;
           case 4: interestAmount = doInterest(minBalance, 3.5);
                   doStatement(creditTx, debitTx, 
                               currentBalance, minBalance, interestAmount);
                   break;
           default: printf("Sorry!!! Invalid choice [1-4 only]\n\n");
                   break;
        }
    } while (option != 4);
    
    printf("\n\nGood Bye!\n\n");
    system("pause");
    return 0;
}

int getUserOption() {
    int option;
    
    printf("\n\nTransaction options: \n");
    printf("1 - Deposit funds (credit transaction) \n");
    printf("2 - Withdraw funds (debit transaction) \n");
    printf("3 - Print statement of account \n");
    printf("4 - Compute interest and exit \n");
    printf("Please indicate your option: \t");
    
    if (scanf("%d", &option) != 1) {
       option = 0;
       scanf("%*s"); 
    }
    return option;
}

void doDeposit(float *cBal) {
     float amt;
     int validInput;
     
     do {
        amt = 0;
        printf("How much do you want to deposit? \t");
        validInput = scanf("%f", &amt);
        if (validInput != 1) 
           scanf("%*s");
     } while (amt <= 0);
     
     *cBal += amt;
     printf("Your current balance is \t $%8.2f\n", *cBal);
     return;
}

void doWithdraw(float *cBal) {
     float amt;
     int validInput;
     
     while (1) {
       do {
         amt = 0;
         printf("How much do you want to withdraw? \t");
         validInput = scanf("%f", &amt);
         if (validInput != 1) 
           scanf("%*s");
       } while (amt <= 0);
     
       if (amt > *cBal){
        printf("Sorry!! you do not have that much money.\n");
        printf("Your current balance is just \t $%8.2f\n", *cBal);
       }
       else {
        *cBal -= amt;
        printf("Your current balance is \t $%8.2f\n", *cBal);
        break;
       }
     }
     return;
}

void doQuery(float cBal, float minBal) {
     
     printf("\t\t Current balance: \t $%8.2f \n", cBal);
     printf("\t\t Minimum balance: \t $%8.2f \n", minBal);
     return;    
}

float doInterest(float minBalance,float intRate) {
      
}

void doStatement(int creditTx, int debitTx, float curentBalance, 
                 float minBalance, float interestAmount) {
                       
}

