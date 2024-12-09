#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>
#include <unistd.h>
#include <time.h>

#define MAXPRED 50
#define MAXPARAM 10
#define MAXSENT 200
#define MAXSUB 1000
#define MAXSTRLEN 200

double rTime, hTime;
int rSteps, hSteps;

int RefuteFlag=0;

typedef struct {
   char name[32];   /* Predicate name */
   int numparam;   /* Number of parameters the predicate requires */
} Predicate;

Predicate predlist[MAXPRED];

typedef struct {
   char con[16];   /* Storage for when the parameter is a constant */
   int var;   /* Storage for when the parameter is a variable */
} Parameter;

typedef struct {
   char comment[MAXSTRLEN]; /* comment from input file */
   int refutePart;          /* set to true if this sentence came from the negated part of the knowledge base */
   int pred[MAXPRED];         /* List of predicates in sentence (indexes into Predicate array) */
   int neg[MAXPRED];         /* Added by T. Andersen. neg[i] set to 1 if predicate indexed by pred[i] is negated */
   int num_pred;             /* Added by T. Andersen.  Stores the number of predicates for this sentence */
   Parameter param[MAXPRED][MAXPARAM];   /* List of parameters for each predicate */
} Sentence;

int sentptr;
Sentence sentlist[MAXSENT];
int nextvar;

/* Returns true if the parameter is a constant */
int constant(Parameter param) {
   if(param.var <= 0 && param.con[0] != '\0') return 1; else return 0;
}

/* Returns true if the parameter is a variable */
int variable(Parameter param) {
   if(param.var > 0 && param.con[0] == '\0') return 1; else return 0;
}

/* Returns true if the parameter is empty */
int empty(Parameter *param) {
   if(param->var <= 0 && param->con[0] == '\0') return 1; else return 0;
}

/* Set the KB to empty */
void InitializeKB(void) {
   sentptr = 0;
   memset(sentlist,0,MAXSENT*sizeof(Sentence));
   memset(predlist,0,MAXPRED*sizeof(Predicate));
   nextvar = 1;
}   

/* Add a predicate to the predicate list */
int AddPredicate(char *name, int numparam) {
   int i;

   i = 0;
   /* Check to see if predicate already in list */
   while(predlist[i].name[0] != '\0' && strcmp(name,predlist[i].name)) i++;
   if(predlist[i].name[0] == '\0') {
      /* Not in predicate list, so add */
      strcpy(predlist[i].name,name); 
      predlist[i].numparam = numparam; 
   } 
   return i; 
} 

/* Standardize apart (Makes sure that each sentence has unique variables) */
void Standardize(char param[MAXPRED][MAXPARAM][16], Parameter sparam[MAXPRED][MAXPARAM], int pred[MAXPRED], int snum) { 
   int i,j,k,sub[256]; 
   
   for(i=0; i<256; i++) sub[i] = -1; 
   for(k=0; k<snum; k++) 
   for(j=0; j<MAXPARAM; j++) {
      i = pred[k];
      if(param[k][j][0] == '\0') continue;
      /*else if(isupper(param[k][j][0])) strcpy(sparam[i][j].con,param[k][j]);*/
      else if(isupper(param[k][j][0])) strcpy(sparam[k][j].con,param[k][j]);
      else {
         if(sub[(unsigned char) param[k][j][0]] == -1) {
            sub[(unsigned char) param[k][j][0]] = nextvar;
            sparam[k][j].var = nextvar;
            nextvar++;
         }
         else {
            sparam[k][j].var = sub[(unsigned char) param[k][j][0]];
         }
      }
   }
}

/* Add a sentence to the KB */
void AddSentence(int neg[MAXPRED],int pred[MAXPRED], char param[MAXPRED][MAXPARAM][16], int snum, char *leftover) {
   int i;

   Standardize(param,sentlist[sentptr].param,pred,snum);
   for(i=0; i<snum; i++) {
      sentlist[sentptr].pred[i] = pred[i];
      sentlist[sentptr].neg[i] = neg[i];
   }
   if(*leftover == '.')
   {
      leftover++;
      leftover[strlen(leftover)-1]=0; /* get rid of new line char */
      strcpy(sentlist[sentptr].comment,leftover);
   }
   sentlist[sentptr].refutePart = RefuteFlag;
   sentlist[sentptr].num_pred = snum;
   sentptr++;
}

/* Convert text version of a sentence into internal representation */
int StringToSentence(char *line) {
   char pname[32],param[MAXPRED][MAXPARAM][16];
   int i,j,p,done,neg[MAXPRED],pred[MAXPRED],snum;

   memset(param,0,MAXPRED*MAXPARAM*16*sizeof(char));
   i = 0;
   snum = 0;
   while((line[i] != '\0') && (line[i] != '\n') && (line[i] != '.')){
      /* 'neg' will keep track of whether the predicate is negated or not */
      neg[snum]=0;
      while(isspace(line[i])) i++;
      if((line[i] == '\0') || (line[i] == '\n') || (line[i] == '.')) break;
      if(line[i] == '!') {
         neg[snum] = 1;
         i++;
         while(isspace(line[i])) i++; /* Added by Tim Andersen.  just in case someone puts space(s) 
                                         between the ! and the beginning of the predicate name */
      }
      /* get predicate name */
      j = i;
      /* while(line[j] != '(' && line[j] != '\0') j++; commented out by Tim Andersen */
      /* The following line added by Tim Andersen to insure that a predicate name only includes text characters */
      while(((line[j] >= 'a') && (line[j] <= 'z')) || ((line[j]>='A') && (line[j]<='Z'))) j++;
      if(line[j] != '(') return 0;  /* we better see the parameter list immediately after the predicate name */
      if(j == i) /* added by Tim Andersen - we better have at least one char in name */
      {
         return 0;  
      }
      memset(pname,0,32*sizeof(char));
      strncpy(pname,&line[i],j-i);

      /* get the parameters */
      done = 0;
      p = 0;
      while(!done) {
         i = j+1;
         while(isspace(line[i])) i++;
         j = i;
         /* while(line[j] != ',' && line[j] != ')' && line[j] != '\0') j++; commented out by Tim Andersen */
      /* The following line added by Tim Andersen to insure that a parameter name only includes text characters */
         while(((line[j] >= 'a') && (line[j] <= 'z')) || ((line[j]>='A') && (line[j]<='Z'))) j++;
         switch(line[j]) {
            case ' ':       /* added by Tim Andersen to allow spaces here */
            case ')': 
            case ',': strncpy(param[snum][p],&line[i],j-i); p++; break;
            break;
            default: return 0;  
         }
         while(isspace(line[j])) j++;
         switch(line[j])
         {
            case ')': done =1;
            case ',':
            break;
            default: return 0;
         }
      }
      i = j+1;
      pred[snum] = AddPredicate(pname,p);
      snum++;
   }
   AddSentence(neg,pred,param,snum,&line[i]);
   return 1;
}

/* Read in a KB from a text file */
int ReadKB(char *filename) {
   FILE *kbfile;
   char line[255];

   kbfile = fopen(filename,"rt");
   if(!kbfile) 
   {
       fprintf(stderr,"File %s not found.\n", filename);
       return 0;
   }
   while(fgets(line,255,kbfile) != 0) {
      if(line[0]=='\n') RefuteFlag=1;  /* the rest after the first blank line should be the negated conclusion */
      else if(!StringToSentence(line)) 
      {
          fprintf(stderr,"Unable to parse line %s\n",line);
          return 0;
      }
   }
   return 1;
}

/* Load a KB from a text file */
void LoadKB(void) {
   char filename[255];

   printf("\nEnter filename: ");
   fgets(filename,255,stdin);
   if(!ReadKB(filename)) InitializeKB();
}

/* Print the current KB to the screen */
void ShowKB(void) {
   int i,j,k,p;
   
   printf("\nCurrent Knowledge Base\n");
   for(i=0; i<sentptr; i++) 
   {
      printf("%d: ",i);
      for(j=0; j<sentlist[i].num_pred; j++) 
      {
         if(sentlist[i].neg[j]) printf("!");
         p = sentlist[i].pred[j];
         printf("%s(",predlist[p].name);
         for(k=0; k<predlist[p].numparam; k++) 
         {
            if(constant(sentlist[i].param[j][k])) printf("%s",sentlist[i].param[j][k].con);
            else printf("%c",'a'+(unsigned char) sentlist[i].param[j][k].var%26);
            if(k<predlist[p].numparam-1) printf(","); else printf(") ");
         }
      }
      if(strlen(sentlist[i].comment)) printf("  //%s",sentlist[i].comment);
      if(sentlist[i].refutePart) printf("  :from refuted part");
      printf("\n");
   }
   printf("\n");
}

/* Allow user to enter a sentence to be added to KB */
void AddKBSentence(void) {
   char sent[255];

   printf("\nEnter sentence: ");
   fgets(sent,255,stdin);
   StringToSentence(sent);
}

/* You must write this function */
void RandomResolve()
{
   rTime=0.0;
   rSteps=0;
   printf("\nRun your RandomResolve routine here\n");

   rTime=100.0; /* change these two lines to reflect the actual time, #steps */
   rSteps=20;

   printf("RandomResolve: #steps = %i, time = %lg\n\n",rSteps, rTime);
}

/* You must write this function */
void HeuristicResolve()
{
   hTime=0.0;
   hSteps=0;
   printf("\nRun your HeuristicResolve routine here\n");

   hTime=50.0; /* change these two lines to reflect the actual time, #steps */
   hSteps=10;
   
   printf("HeuristicResolve: #steps = %i, time = %lg\n\n",hSteps, hTime);
}

/* You must write this function */
int Unify(int sent1, int sent2) {}

/* You must write this function */
void Resolve(void) {
   RandomResolve();
   HeuristicResolve();
   printf("Heuristic vs Random ratios:  hSteps/rSteps = %lg, hTime/rTime = %lg\n\n",(double)hSteps/(double)rSteps, hTime/rTime);
}

/* User enters a the negation of their query.  This is added to KB, and then KB is resolved to find solution */
void ProveQuery(void) {
   char query[255];

   printf("\nEnter negated query: ");
   fgets(query,255,stdin);
   StringToSentence(query);
   Resolve();
}

int main(int argc, char *argv[])
{
   char *filename,choice[64];
   int done;

   srand((unsigned int) time(0));
   if(argc > 2) {
      printf("Usage: prover [filename]\n");
      exit(0);
   }
   InitializeKB();
   if(argc == 2) {
      filename = argv[1];
      if(!ReadKB(filename)) 
      {
         printf("Syntax error in knowledge base\n");
         exit(0);
      }
      ShowKB();
      Resolve();
      exit(0);
   }
   done = 0;
   while(!done) {   
      do {
         system("clear");
         printf("\nMain Menu");
         printf("\n---------");
         printf("\n(A)dd sentence to database");
         printf("\n(C)lear database");
         printf("\n(L)oad database");
         printf("\n(S)how database");
         printf("\n(P)rove query");
         printf("\n(Q)uit program");
         printf("\n\nChoice: ");
         fgets(choice,64,stdin);
      } 
      while(choice[0] != 'a' && choice[0] != 'c' && choice[0] != 'l' && 
            choice[0] != 'p' && choice[0] != 's' && choice[0] != 'q');
      switch(choice[0]) {
         case 'a': AddKBSentence(); break;
         case 'c': InitializeKB(); break;
         case 'l': InitializeKB(); LoadKB(); break;
         case 's': {
                       char temp[100];
                       ShowKB(); 
                       printf("Press enter to continue... ");
                       fgets(temp,100,stdin);
                       break;
                   }
         case 'p': ProveQuery(); break;
         case 'q': done = 1; break;
      }
   }
   return 0;
}

