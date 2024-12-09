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

/* Function prototypes */
int Unify(int sent1, int sent2);

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
   clock_t start = clock();
   rTime = 0.0;
   rSteps = 0;
   int sent_generated = 0;
   int initial_sentptr = sentptr;

   printf("\nRunning Random Resolve (press Ctrl-c to cancel)...\n");

   while (sentptr < MAXSENT) {
      // Randomly select two sentences
      int sent1 = rand() % sentptr;
      int sent2 = rand() % sentptr;

      // Skip if same sentence
      if (sent1 == sent2) continue;

      // Try to unify and resolve
      if (Unify(sent1, sent2)) {
         rSteps++;
         sent_generated++;

         // Print the selected sentences
         printf("    %d:                               ", sent1);
         for (int i = 0; i < sentlist[sent1].num_pred; i++) {
            if (sentlist[sent1].neg[i]) printf("!");
            printf("%s(", predlist[sentlist[sent1].pred[i]].name);
            for (int j = 0; j < predlist[sentlist[sent1].pred[i]].numparam; j++) {
               if (constant(sentlist[sent1].param[i][j])) 
                  printf("%s", sentlist[sent1].param[i][j].con);
               else 
                  printf("%c", 'a' + (unsigned char)sentlist[sent1].param[i][j].var % 26);
               if (j < predlist[sentlist[sent1].pred[i]].numparam - 1) printf(",");
            }
            printf(") ");
         }
         printf("\n");

         printf("    %d:                               ", sent2);
         for (int i = 0; i < sentlist[sent2].num_pred; i++) {
            if (sentlist[sent2].neg[i]) printf("!");
            printf("%s(", predlist[sentlist[sent2].pred[i]].name);
            for (int j = 0; j < predlist[sentlist[sent2].pred[i]].numparam; j++) {
               if (constant(sentlist[sent2].param[i][j])) 
                  printf("%s", sentlist[sent2].param[i][j].con);
               else 
                  printf("%c", 'a' + (unsigned char)sentlist[sent2].param[i][j].var % 26);
               if (j < predlist[sentlist[sent2].pred[i]].numparam - 1) printf(",");
            }
            printf(") ");
         }
         printf("\n--\n");

         // Check if we found a contradiction
         if (sentlist[sentptr-1].num_pred == 0) {
            printf("Sentences %d and %d Complete the Proof!\n", sent1, sent2);
            break;
         }
      }
   }

   if (sentptr >= MAXSENT) {
      printf("FAILED to resolve! KB is FULL.\n");
   } else if (sentptr == initial_sentptr) {
      printf("FAILED to resolve! There are no more possible resolutions.\n");
   }

   rTime = (double)(clock() - start) / CLOCKS_PER_SEC;
   printf("RandomResolve: #sent-generated = %d, #steps = %d, time = %lg\n\n", sent_generated, rSteps, rTime);
}

/* You must write this function */
void HeuristicResolve() {
    clock_t start = clock();
    hTime = 0.0;
    hSteps = 0;
    int sent_generated = 0;
    int initial_sentptr = sentptr;
    
    unsigned char *tried = (unsigned char*)calloc((MAXSENT * MAXSENT) / 8 + 1, 1);
    if (!tried) return;
    
    printf("\nRunning Heuristic Resolve...\n");
    
    while (sentptr < MAXSENT) {
        int best_sent1 = -1;
        int best_sent2 = -1;
        int best_score = -1;
        
        for (int i = 0; i < sentptr; i++) {
            if (sentlist[i].num_pred == 0) continue;
            hSteps++;
            
            for (int j = i + 1; j < sentptr; j++) {
                if (sentlist[j].num_pred == 0) continue;
                
                int idx = (i * MAXSENT + j) / 8;
                int bit = (i * MAXSENT + j) % 8;
                if (tried[idx] & (1 << bit)) continue;

                // Print each attempted resolution step
                printf("Trying resolution between:\n");
                printf("    %d:                               ", i);
                for (int pi = 0; pi < sentlist[i].num_pred; pi++) {
                    if (sentlist[i].neg[pi]) printf("!");
                    printf("%s(", predlist[sentlist[i].pred[pi]].name);
                    for (int pj = 0; pj < predlist[sentlist[i].pred[pi]].numparam; pj++) {
                        if (constant(sentlist[i].param[pi][pj])) 
                            printf("%s", sentlist[i].param[pi][pj].con);
                        else 
                            printf("%c", 'a' + (unsigned char)sentlist[i].param[pi][pj].var % 26);
                        if (pj < predlist[sentlist[i].pred[pi]].numparam - 1) printf(",");
                    }
                    printf(") ");
                }
                printf("\n");

                printf("    %d:                               ", j);
                for (int pi = 0; pi < sentlist[j].num_pred; pi++) {
                    if (sentlist[j].neg[pi]) printf("!");
                    printf("%s(", predlist[sentlist[j].pred[pi]].name);
                    for (int pj = 0; pj < predlist[sentlist[j].pred[pi]].numparam; pj++) {
                        if (constant(sentlist[j].param[pi][pj])) 
                            printf("%s", sentlist[j].param[pi][pj].con);
                        else 
                            printf("%c", 'a' + (unsigned char)sentlist[j].param[pi][pj].var % 26);
                        if (pj < predlist[sentlist[j].pred[pi]].numparam - 1) printf(",");
                    }
                    printf(") ");
                }
                printf("\n--\n");

                // Rest of the existing scoring logic
                int found_complement = 0;
                int score = 0;
                
                Sentence *s1 = &sentlist[i];
                Sentence *s2 = &sentlist[j];
                
                for (int pi = 0; !found_complement && pi < s1->num_pred; pi++) {
                    for (int pj = 0; pj < s2->num_pred; pj++) {
                        if (s1->pred[pi] == s2->pred[pj] && s1->neg[pi] != s2->neg[pj]) {
                            found_complement = 1;
                            score = 50;
                            break;
                        }
                    }
                }
                
                if (!found_complement) continue;

                score += (s1->refutePart + s2->refutePart) * 100;
                score -= (s1->num_pred + s2->num_pred) * 2;
                
                if (score > best_score) {
                    best_score = score;
                    best_sent1 = i;
                    best_sent2 = j;
                }
            }
        }
        
        if (best_sent1 == -1) break;
        
        int idx = (best_sent1 * MAXSENT + best_sent2) / 8;
        int bit = (best_sent1 * MAXSENT + best_sent2) % 8;
        tried[idx] |= (1 << bit);
        
        printf("    %d:                               ", best_sent1);
        for (int i = 0; i < sentlist[best_sent1].num_pred; i++) {
            if (sentlist[best_sent1].neg[i]) printf("!");
            printf("%s(", predlist[sentlist[best_sent1].pred[i]].name);
            for (int j = 0; j < predlist[sentlist[best_sent1].pred[i]].numparam; j++) {
                if (constant(sentlist[best_sent1].param[i][j])) 
                    printf("%s", sentlist[best_sent1].param[i][j].con);
                else 
                    printf("%c", 'a' + (unsigned char)sentlist[best_sent1].param[i][j].var % 26);
                if (j < predlist[sentlist[best_sent1].pred[i]].numparam - 1) printf(",");
            }
            printf(") ");
        }
        printf("\n");

        printf("    %d:                               ", best_sent2);
        for (int i = 0; i < sentlist[best_sent2].num_pred; i++) {
            if (sentlist[best_sent2].neg[i]) printf("!");
            printf("%s(", predlist[sentlist[best_sent2].pred[i]].name);
            for (int j = 0; j < predlist[sentlist[best_sent2].pred[i]].numparam; j++) {
                if (constant(sentlist[best_sent2].param[i][j])) 
                    printf("%s", sentlist[best_sent2].param[i][j].con);
                else 
                    printf("%c", 'a' + (unsigned char)sentlist[best_sent2].param[i][j].var % 26);
                if (j < predlist[sentlist[best_sent2].pred[i]].numparam - 1) printf(",");
            }
            printf(") ");
        }
        printf("\n--\n");
        
        if (Unify(best_sent1, best_sent2)) {
            hSteps++;
            sent_generated++;
            
            if (sentlist[sentptr-1].num_pred == 0) {
                printf("Sentences %d and %d Complete the Proof!\n", best_sent1, best_sent2);
                free(tried);
                break;
            }
        }
    }
    
    if (sentptr >= MAXSENT) {
        printf("FAILED to resolve! KB is FULL.\n");
    } else if (sentptr == initial_sentptr) {
        printf("FAILED to resolve! No more resolutions possible.\n");
    }
    
    hTime = (double)(clock() - start) / CLOCKS_PER_SEC;
    printf("HeuristicResolve: #sent-generated = %d, #steps = %d, time = %lg\n\n", 
           sent_generated, hSteps, hTime);
}

/* You must write this function */
int Unify(int sent1, int sent2) {
    for (int i = 0; i < sentlist[sent1].num_pred; i++) {
        int pred1 = sentlist[sent1].pred[i];
        int neg1 = sentlist[sent1].neg[i];
        
        for (int j = 0; j < sentlist[sent2].num_pred; j++) {
            int pred2 = sentlist[sent2].pred[j];
            int neg2 = sentlist[sent2].neg[j];
            
            if (pred1 == pred2 && neg1 != neg2) {
                int can_unify = 1;
                Parameter substitutions[MAXSUB];
                int num_subs = 0;
                
                for (int k = 0; k < predlist[pred1].numparam; k++) {
                    Parameter param1 = sentlist[sent1].param[i][k];
                    Parameter param2 = sentlist[sent2].param[j][k];
                    
                    if (constant(param1) && constant(param2)) {
                        if (strcmp(param1.con, param2.con) != 0) {
                            can_unify = 0;
                            break;
                        }
                    }
                    else if (constant(param1) && variable(param2)) {
                        substitutions[num_subs] = param1;
                        substitutions[num_subs].var = param2.var;
                        num_subs++;
                    }
                    else if (variable(param1) && constant(param2)) {
                        substitutions[num_subs] = param2;
                        substitutions[num_subs].var = param1.var;
                        num_subs++;
                    }
                    else if (variable(param1) && variable(param2)) {
                        substitutions[num_subs].con[0] = '\0';
                        substitutions[num_subs].var = param2.var;
                        num_subs++;
                        param2.var = param1.var;
                    }
                }
                
                if (can_unify) {
                    Sentence new_sent;
                    new_sent.num_pred = 0;
                    new_sent.refutePart = sentlist[sent1].refutePart || sentlist[sent2].refutePart;
                    
                    for (int k = 0; k < sentlist[sent1].num_pred; k++) {
                        if (k != i) {
                            new_sent.pred[new_sent.num_pred] = sentlist[sent1].pred[k];
                            new_sent.neg[new_sent.num_pred] = sentlist[sent1].neg[k];
                            for (int p = 0; p < predlist[sentlist[sent1].pred[k]].numparam; p++) {
                                new_sent.param[new_sent.num_pred][p] = sentlist[sent1].param[k][p];
                                if (variable(new_sent.param[new_sent.num_pred][p])) {
                                    for (int s = 0; s < num_subs; s++) {
                                        if (new_sent.param[new_sent.num_pred][p].var == substitutions[s].var) {
                                            if (substitutions[s].con[0] != '\0')
                                                strcpy(new_sent.param[new_sent.num_pred][p].con, substitutions[s].con);
                                            else
                                                new_sent.param[new_sent.num_pred][p].var = substitutions[s].var;
                                        }
                                    }
                                }
                            }
                            new_sent.num_pred++;
                        }
                    }
                    
                    for (int k = 0; k < sentlist[sent2].num_pred; k++) {
                        if (k != j) {
                            new_sent.pred[new_sent.num_pred] = sentlist[sent2].pred[k];
                            new_sent.neg[new_sent.num_pred] = sentlist[sent2].neg[k];
                            for (int p = 0; p < predlist[sentlist[sent2].pred[k]].numparam; p++) {
                                new_sent.param[new_sent.num_pred][p] = sentlist[sent2].param[k][p];
                                if (variable(new_sent.param[new_sent.num_pred][p])) {
                                    for (int s = 0; s < num_subs; s++) {
                                        if (new_sent.param[new_sent.num_pred][p].var == substitutions[s].var) {
                                            if (substitutions[s].con[0] != '\0')
                                                strcpy(new_sent.param[new_sent.num_pred][p].con, substitutions[s].con);
                                            else
                                                new_sent.param[new_sent.num_pred][p].var = substitutions[s].var;
                                        }
                                    }
                                }
                            }
                            new_sent.num_pred++;
                        }
                    }
                    
                    sentlist[sentptr] = new_sent;
                    sentptr++;
                    return 1;
                }
            }
        }
    }
    return 0;
}

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

