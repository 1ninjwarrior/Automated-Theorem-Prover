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

int Unify(int sent1, int sent2);

void ShowSentence(int index);
void PrintResolutionPath(int sent1, int sent2);

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
      else if(isupper(param[k][j][0])) {
          // Constants should be stored as constants
          strcpy(sparam[k][j].con, param[k][j]);
          sparam[k][j].var = 0;  // Ensure var is 0 for constants
      }
      else {
         // Variables should have empty con field
         sparam[k][j].con[0] = '\0';
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

/* Helper function to check if two sentences can be resolved */
int canResolve(int sent1, int sent2) {
    return Unify(sent1, sent2);
}

/* RandomResolve implementation */
void RandomResolve() {
    clock_t start = clock();
    rSteps = 0;
    int maxAttempts = 1000;  // Prevent infinite loops
    
    while (rSteps < maxAttempts) {
        // Randomly select two sentences
        int s1 = rand() % sentptr;
        int s2 = rand() % sentptr;
        
        if (s1 != s2 && canResolve(s1, s2)) {
            rSteps++;
            // If one sentence is from refuted part and other isn't, we found a potential path
            if (sentlist[s1].refutePart != sentlist[s2].refutePart) {
                break;
            }
        }
    }
    
    rTime = ((double)(clock() - start)) / CLOCKS_PER_SEC;
}

/* HeuristicResolve implementation using set-of-support strategy */
void HeuristicResolve() {
    clock_t start = clock();
    hSteps = 0;
    
    // Set of support strategy: Start with sentences from refuted part
    for (int i = 0; i < sentptr && hSteps < 1000; i++) {
        if (sentlist[i].refutePart) {
            // Try to resolve with non-refuted sentences first
            for (int j = 0; j < sentptr; j++) {
                if (!sentlist[j].refutePart && canResolve(i, j)) {
                    hSteps++;
                    // Found a potential resolution path
                    if (hSteps > 0) {
                        break;
                    }
                }
            }
        }
    }
    
    hTime = ((double)(clock() - start)) / CLOCKS_PER_SEC;
}

/* Structure to track resolution steps */
typedef struct {
    int parent1;
    int parent2;
    int resolvedPred1;
    int resolvedPred2;
    Sentence result;
} ResolutionStep;

ResolutionStep steps[MAXSENT];
int stepCount = 0;

/* Create a new resolved sentence from two parent sentences */
Sentence resolveSentences(int sent1, int sent2, int pred1, int pred2) {
    Sentence newSent;
    memset(&newSent, 0, sizeof(Sentence));
    
    // Create substitution map
    int varMap[MAXSUB] = {0};
    int nextNewVar = nextvar;
    
    // Build substitution map
    for (int k = 0; k < predlist[sentlist[sent1].pred[pred1]].numparam; k++) {
        Parameter p1 = sentlist[sent1].param[pred1][k];
        Parameter p2 = sentlist[sent2].param[pred2][k];
        
        if (variable(p1) && constant(p2)) {
            varMap[p1.var] = -(k + 1);
            strcpy(newSent.param[0][k].con, p2.con);
        } else if (constant(p1) && variable(p2)) {
            varMap[p2.var] = k + 1;
            strcpy(newSent.param[0][k].con, p1.con);
        } else if (variable(p1) && variable(p2)) {
            if (varMap[p1.var] == 0 && varMap[p2.var] == 0) {
                varMap[p1.var] = nextNewVar;
                varMap[p2.var] = nextNewVar;
                nextNewVar++;
            }
        }
    }
    
    // Copy predicates from both sentences except resolved ones
    int newPredCount = 0;
    
    // Copy from sent1
    for (int i = 0; i < sentlist[sent1].num_pred; i++) {
        if (i != pred1) {
            newSent.pred[newPredCount] = sentlist[sent1].pred[i];
            newSent.neg[newPredCount] = sentlist[sent1].neg[i];
            
            // Apply substitutions
            for (int k = 0; k < predlist[sentlist[sent1].pred[i]].numparam; k++) {
                Parameter p = sentlist[sent1].param[i][k];
                if (variable(p) && varMap[p.var] != 0) {
                    if (varMap[p.var] < 0) {
                        // Map to constant
                        strcpy(newSent.param[newPredCount][k].con, 
                               sentlist[sent2].param[pred2][-varMap[p.var]-1].con);
                        newSent.param[newPredCount][k].var = 0;
                    } else {
                        // Map to new variable
                        newSent.param[newPredCount][k].var = varMap[p.var];
                        newSent.param[newPredCount][k].con[0] = '\0';
                    }
                } else {
                    newSent.param[newPredCount][k] = p;
                }
            }
            newPredCount++;
        }
    }
    
    // Copy from sent2 (similar logic for sent2)
    for (int i = 0; i < sentlist[sent2].num_pred; i++) {
        if (i != pred2) {
            newSent.pred[newPredCount] = sentlist[sent2].pred[i];
            newSent.neg[newPredCount] = sentlist[sent2].neg[i];
            
            for (int k = 0; k < predlist[sentlist[sent2].pred[i]].numparam; k++) {
                Parameter p = sentlist[sent2].param[i][k];
                if (variable(p) && varMap[p.var] != 0) {
                    if (varMap[p.var] < 0) {
                        strcpy(newSent.param[newPredCount][k].con, 
                               sentlist[sent1].param[pred1][-varMap[p.var]-1].con);
                        newSent.param[newPredCount][k].var = 0;
                    } else {
                        newSent.param[newPredCount][k].var = varMap[p.var];
                        newSent.param[newPredCount][k].con[0] = '\0';
                    }
                } else {
                    newSent.param[newPredCount][k] = p;
                }
            }
            newPredCount++;
        }
    }
    
    newSent.num_pred = newPredCount;
    nextvar = nextNewVar;
    return newSent;
}

/* Main resolution function */
void Resolve() {
    stepCount = 0;
    int contradiction = 0;
    int maxSteps = 100;  // Limit steps to prevent infinite loops
    
    printf("\nStarting Resolution Process:\n");
    printf("---------------------------\n");
    fflush(stdout);
    
    // Start with sentences from refuted part
    for(int i = 0; i < sentptr && !contradiction && stepCount < maxSteps; i++) {
        if(sentlist[i].refutePart) {
            printf("\nTrying to resolve with sentence %d: ", i);
            ShowSentence(i);
            
            for(int j = 0; j < sentptr && !contradiction; j++) {
                if(i == j) continue;
                
                // Try to resolve these sentences
                for(int pred1 = 0; pred1 < sentlist[i].num_pred; pred1++) {
                    for(int pred2 = 0; pred2 < sentlist[j].num_pred; pred2++) {
                        if(sentlist[i].pred[pred1] == sentlist[j].pred[pred2] && 
                           sentlist[i].neg[pred1] != sentlist[j].neg[pred2]) {
                            
                            // Check if parameters can be unified
                            int canUnify = 1;
                            for(int k = 0; k < predlist[sentlist[i].pred[pred1]].numparam; k++) {
                                Parameter p1 = sentlist[i].param[pred1][k];
                                Parameter p2 = sentlist[j].param[pred2][k];
                                
                                // If both are constants, they must match exactly
                                if(constant(p1) && constant(p2)) {
                                    if(strcmp(p1.con, p2.con) != 0) {
                                        canUnify = 0;
                                        break;
                                    }
                                }
                            }
                            
                            if(!canUnify) continue;
                            
                            printf("\nResolution Step %d:\n", stepCount + 1);
                            printf("Resolving sentences:\n");
                            printf("  Sentence %d: ", i);
                            ShowSentence(i);
                            printf("  Sentence %d: ", j);
                            ShowSentence(j);
                            
                            // Create resolved sentence
                            Sentence newSent = resolveSentences(i, j, pred1, pred2);
                            
                            // Check if resolution was valid
                            if(newSent.num_pred == -1) continue;
                            
                            // Add the resolved sentence to KB
                            sentlist[sentptr] = newSent;
                            sentlist[sentptr].refutePart = 1;
                            
                            printf("  Resolved Result: ");
                            ShowSentence(sentptr);
                            
                            // Check if we found a contradiction (empty clause)
                            if(newSent.num_pred == 0) {
                                printf("\nContradiction found! Proof complete.\n");
                                printf("Final Resolution Path:\n");
                                PrintResolutionPath(i, j);
                                contradiction = 1;
                                break;
                            }
                            
                            sentptr++;
                            stepCount++;
                        }
                    }
                    if(contradiction) break;
                }
            }
        }
    }
    
    if(!contradiction) {
        printf("\nNo contradiction found. Query cannot be proved.\n");
    }
    fflush(stdout);
}

// Helper function to show a single sentence
void ShowSentence(int index) {
    for(int j = 0; j < sentlist[index].num_pred; j++) {
        if(sentlist[index].neg[j]) printf("!");
        int p = sentlist[index].pred[j];
        printf("%s(", predlist[p].name);
        for(int k = 0; k < predlist[p].numparam; k++) {
            if(constant(sentlist[index].param[j][k])) 
                printf("%s", sentlist[index].param[j][k].con);
            else 
                printf("%c", 'a' + (unsigned char)sentlist[index].param[j][k].var % 26);
            if(k < predlist[p].numparam-1) printf(",");
        }
        printf(") ");
    }
    printf("\n");
}

// Helper function to print the resolution path that led to contradiction
void PrintResolutionPath(int sent1, int sent2) {
    printf("  Final resolving sentences:\n");
    printf("    Sentence %d: ", sent1);
    ShowSentence(sent1);
    printf("    Sentence %d: ", sent2);
    ShowSentence(sent2);
}

/* User enters a the negation of their query.  This is added to KB, and then KB is resolved to find solution */
void ProveQuery(void) {
   char query[255];
   char temp[100];

   printf("\nEnter negated query: ");
   fgets(query,255,stdin);
   StringToSentence(query);
   Resolve();
   
   printf("\nPress enter to continue...");
   fgets(temp,100,stdin);
}

/* Unify attempts to unify two sentences. Returns 1 if successful, 0 if not */
int Unify(int sent1, int sent2) {
    // Check for empty sentences
    if (sentlist[sent1].num_pred == 0 || sentlist[sent2].num_pred == 0) {
        return 0;
    }

    for (int i = 0; i < sentlist[sent1].num_pred; i++) {
        for (int j = 0; j < sentlist[sent2].num_pred; j++) {
            // Check if predicates match and have opposite signs
            if (sentlist[sent1].pred[i] == sentlist[sent2].pred[j] && 
                sentlist[sent1].neg[i] != sentlist[sent2].neg[j]) {
                
                // Create substitution map for variables
                int varMap[MAXSUB] = {0};
                int canUnify = 1;
                
                // Check each parameter
                for (int k = 0; k < predlist[sentlist[sent1].pred[i]].numparam; k++) {
                    Parameter p1 = sentlist[sent1].param[i][k];
                    Parameter p2 = sentlist[sent2].param[j][k];
                    
                    // Case 1: Both constants
                    if (constant(p1) && constant(p2)) {
                        if (strcmp(p1.con, p2.con) != 0) {
                            canUnify = 0;
                            break;
                        }
                    }
                    // Case 2: First is variable, second is constant
                    else if (variable(p1) && constant(p2)) {
                        if (varMap[p1.var] == 0) {
                            varMap[p1.var] = -(k + 1); // Store negative to indicate constant
                        } else if (varMap[p1.var] != -(k + 1)) {
                            canUnify = 0;
                            break;
                        }
                    }
                    // Case 3: First is constant, second is variable
                    else if (constant(p1) && variable(p2)) {
                        if (varMap[p2.var] == 0) {
                            varMap[p2.var] = k + 1;
                        } else if (varMap[p2.var] != k + 1) {
                            canUnify = 0;
                            break;
                        }
                    }
                    // Case 4: Both variables
                    else if (variable(p1) && variable(p2)) {
                        if (varMap[p1.var] == 0 && varMap[p2.var] == 0) {
                            varMap[p1.var] = p2.var;
                        } else if (varMap[p1.var] != varMap[p2.var]) {
                            canUnify = 0;
                            break;
                        }
                    }
                }
                if (canUnify) return 1;
            }
        }
    }
    return 0;
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

