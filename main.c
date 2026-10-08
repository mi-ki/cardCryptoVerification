#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <regex.h> 

#include <cjson/cJSON.h> 


/*TODO: think about what should be passed to main and how
   - numberPossiblePermutations -> for permutationSet[X][Y]
   - maybe N, NUM_SYM, COMMIT, NUMBER_PROBABILITIES, NUMBER_START_SEQS (for error handling?)
   - maybe L
   - maybe TURN, SHUFFLE
*/

/* TODO: think about "hardcoded" stuff
   - structure of json objects??
   - turnPosition? -> vlt ebene höher?
   - ??? 
*/

// TODO: Variable names

#define BUFFER_SIZE 2048
#define BUFFER_SIZE_SMALL 64

#define TURN 0 // TODO: maybe take from the same  (header)file as findTwoCardProtocol? 
#define SHUFFLE 1
#define RESULT 2

// TODO: unterscheidung trace error und data not valid wirklich notwendig?
typedef enum  { 
   NO_ERROR = 0,
   TRACE_ERROR = -1, 
   BAD_MALLOC = -2,
   DATA_NOT_VALID = -3,
   LOCATION_NOT_FOUND = -4,
   BAD_REGEX = -5,
   CRITICAL_TRACE_ERROR = -6
} ErrorCode;


typedef enum {
   PARSE_NONE,
   PARSE_DATA,
   PARSE_STATE,
   PARSE_PPS,
   PARSE_FRACTION,
   PARSE_SEQUENCE,
   PARSE_SYMBOLS,
   PARSE_ACTION, 
   PARSE_AB,
   PARSE_PERMSETSIZE,
   PARSE_PERMSETVALUE,
   CHECK_FORMAT_SPECIFIER,
} FunctionCodes;

int numberPossibleSequences = 0;
int numberPossiblePermutations = 0;
int numberProbabilities = 0;
int n = 0;
int l = 0;
int numSym = 0;


/** 
 * All values in permutationSet are separate objects in the cbmc output (i.e. they must be parsed separately)
 * The first <numberPossiblePermutations> objects in the output for every generated permutationSet belong to 
 * values before permutations are stored in the array, so the can be ignored. 
 * permSetCounter counts these objects. After <numberPossiblePermutations>, permutationSetPreAssign is set to false. 
 * The next permSetSize*N objects contain the actual permutations and must be stored
 */
int permutationSetPreAssign = true;
int permSetCounter = 0;
int permSetSize = 0;

// Index of current state in reachableStates
int next = 0;

// Variable for turnPosition and action (shuffle, turn, result).
int turnPosition = -1;
int currentAction = -1;

// Index of the state
int currentStateIndex = 0;

int currentSequence = -1;
int currentSymbol = -1;
int currentFraction = -1;


int currentParsingStep = PARSE_NONE; 
int prevParsingStep = PARSE_NONE;

/**
 * States are parsed using the objects belonging to reachableStates and possiblePostStates. 
 * reachableStates contains all reachable states on the path from the start state to the result but not all possible states after a turn.
 * Those can be taken from objects belonging to possiblePostStates. 
 * Because the state that is chosen after turn occurs in both data structures, we skip parsing the first state in reachableStates after a turn.
 */
int skipNextState = false; 

/**
 *  Structs for different actions. All structs store the index of the previous and te following state
 */
struct Shuffle {
   int fromState;
   int toState;
   int permSetSize;
   int *permutationSet;
};

struct Turn {
   int fromState;
   int toState; 
   int turnedCard; 
   int turnPosition;
};

// a and b are the positions of the cards that encode the result
struct Result {
   int fromState;
   int a;
   int b;
};

// "Wrapper" to make storing all actions in an array possible; actiontype determines the action
struct Action {
  int actiontype;
  union {
      struct Shuffle *shuffle;
      struct Turn *turn;
      struct Result *result;
  };
};

// Struct for sequence. To simplfy the data structure for probabilities, numerators and denominators are stored in distinct arrays
struct Sequence {
   int *symbols;
   int *nums;
   int *dens;
}; 

struct State {
   int index;
   struct Sequence **sequences;
};

int maxGraphSize = 0;
struct Action** actions;
struct State** states;

/**
 * a and b occur every time when it is checked if a state is a final state, 
 * but only the last values are needed, so they are stored in this array and
 * are overwritten each time when they are parsed
 */
int resultPositions[2];  

// Index of the state in possiblePostStates that is chosen after turn
int chosenTurnStateIdx = 0;  

// Helper variable to store the index of the last state in the path
// Necessary to determine the state where an action after a turn comes from
int stateFrom = 0;

void handleInternalError(int errorcode){
   switch (errorcode){
      case BAD_MALLOC:
         printf("Internal Error: failed to allocate memory\n");
         break;
      case BAD_REGEX:
         printf("Internal Error: failed to compile regex\n");
         break;
      default:
         printf("Internal Error\n");
         break;
   }
   exit(1);
}

// Memory cleanup
void freeState(struct State *state){
   for (int i = 0; i < numberPossibleSequences; i++){
      if(state->sequences[i] != NULL){
         free(state->sequences[i]->symbols);
         free(state->sequences[i]->nums);
         free(state->sequences[i]->dens);
         free(state->sequences[i]);
      }
   }
   free(state->sequences);
   free(state);
}

void freeAction(struct Action *action){
   if(action->actiontype == TURN){
      free(action->turn);
   } else if (action->actiontype == SHUFFLE){
      free(action->shuffle->permutationSet);
      free(action->shuffle);
   } else if (action->actiontype == RESULT){
      free(action->result);
   }
   free(action);
}

int cleanJSON(char *jsonBuffer, char *commentsBuffer, cJSON *json){
   // delete the JSON object
   cJSON_Delete(json);
   if (jsonBuffer){
      free(jsonBuffer);
   }
   if (commentsBuffer){
      free(commentsBuffer);
   }
   return EXIT_SUCCESS;
}

int cleanStructs(){
   // Free memory 
   for(int i = 0; i < maxGraphSize; i++){
      if(states[i]){
         freeState(states[i]);
      }
   }
   for(int i = 0; i < maxGraphSize; i++){
      if(actions[i]){
         freeAction(actions[i]);
      }
   }

   free(actions);
   free(states);

   return EXIT_SUCCESS;
}

// TODO nicht nur print
// TODO clean up?
void addErrorMessage(bool isTraceError, int arraySizeError, int denNum, char* str){
   printf("IN ADD_ERRORMESSAGE ");
   if(isTraceError){
      printf("TRACE ERROR: ");
   }
   printf("Error parsing ");

   switch (currentParsingStep){
      case CHECK_FORMAT_SPECIFIER:
         printf("format specifier (checkFormatSpecifier): wrong format specifier (%s)\n", str);
         break;
      case PARSE_DATA:
         printf("numeric value (parseData): ");

         if(denNum < 0){
            printf("data missing or value of key \"data\" is not a string\n\n");
         } else {
            printf("data (%s) has wrong format or value is missing\n", str);
         }
         break;
      case PARSE_FRACTION:
         printf("fraction (parseFraction), sequence %i", currentSequence);

         if(!isTraceError){
            if (currentFraction < 0){
               printf(": JSON data for probabilities is missing or has wrong format\n");
            } else {
               printf(", fraction %i: ", currentFraction);
               if(denNum < 0){
                  printf("JSON data is missing or has wrong format\n");
               } else {
                  printf("numerator or denominator is invalid\n");
               }
            }
         } else {
            if (currentFraction < 0){
               printf(": wrong number of probabilities. Should be %i, got %i\n", numberProbabilities, arraySizeError); 
            } else {
               printf(", fraction %i: assumed array of length 2 (numerator, denimoninator), but length is %i\n", currentFraction, arraySizeError);
            } 
            
         }
         break;
      case PARSE_SYMBOLS:
         printf("symbols (parseSymbols), sequence %i", currentSequence);

         if(!isTraceError){
            if(currentSymbol < 0){
               printf(": JSON data for symbols is missing or has wrong format\n");
            } else {
               printf(", symbol %i: JSON data is missing or has wrong format\n", currentSymbol);
            }
         } else {
            printf(": assumed array %i symbols, but got %i\n", n, arraySizeError);
         }
         break;
      case PARSE_STATE:
         printf("state (parseState)");
         if(currentSequence >= 0 && arraySizeError < 0){
            printf(", sequence %i: JSON data is missing or has wrong format\n", currentSequence);
         } else if(currentSequence < 0 && arraySizeError < 0) {
            printf(": JSON data for sequences is missing\n");
         } else {
            printf(": assumed array of length 2 (symbols, fractions), but length is %i\n", arraySizeError);
         }
         break;
      default:
         printf("blublu\n");
   }
}

// TODO comment
void setParsingStep(int step){
   prevParsingStep = currentParsingStep;
   currentParsingStep = step;
}

// TODO comment
void resetParsingStep(){
   currentParsingStep = prevParsingStep;
}

// Checks if format specifier is valid (integer, long, etc.)
int checkFormatSpecifier(char *name){
   setParsingStep(CHECK_FORMAT_SPECIFIER);
   int reti;
   regex_t regex;
   reti = regcomp( &regex, "^[l]?[l]?[(i|u)]?$", REG_EXTENDED);
   if (reti) {  
      handleInternalError(BAD_REGEX);
   }
   reti = regexec(&regex, name, 0, NULL, 0);
   regfree(&regex);
   if (!reti) {
      return NO_ERROR;
   }
   addErrorMessage(false, -1, -1, name);
   return DATA_NOT_VALID;
}



// Parse unsigned integer value in "data" key from "value" of json object
int parseData(cJSON *valueObject){
   setParsingStep(PARSE_DATA);
   cJSON *data = cJSON_GetObjectItemCaseSensitive(valueObject, "data");
   if(!data || !cJSON_IsString(data)){  // Errorhandling if data is missing 
      //TODO entfernen, wenn  klar ist wo das hier "dead code" ist
      printf("DOCH KEIN DEAD CODE????\n");
      addErrorMessage(false, -1, -1, NULL);
      return DATA_NOT_VALID;  
   }

   int dataValue = 0;
   char fmt[BUFFER_SIZE_SMALL] = {0};
   if (sscanf(data->valuestring, "%i%s", &dataValue, fmt) != 0){
      int fsp = checkFormatSpecifier(fmt);
      resetParsingStep();
      if (fsp >= 0){  // Errorhandling if data has not the correct format
         return dataValue;
      }
   }
   addErrorMessage(false, -1, 0, data->valuestring);
   return DATA_NOT_VALID; 
}


// Adds result action to the actions array
int addResult(){
   struct Action *newAction = malloc(sizeof(struct Action));
   struct Result *result = malloc(sizeof(struct Result));

   if (!newAction || !result){
      printf("Internal Error in Parser: memory not allocated\n");
      handleInternalError(BAD_MALLOC);
   }

   if (resultPositions[0] == resultPositions[1]){
      printf("Error: positions of result cards are invalid\n");
      return DATA_NOT_VALID;
   }

   // Add result to array for actions 
   *result = (struct Result){currentStateIndex, resultPositions[0], resultPositions[1]};
   *newAction = (struct Action){.actiontype = RESULT, .result = result};
   actions[currentStateIndex+1] = newAction;

   return NO_ERROR;
}


// TODO: this prints permutations ín the way they are in the code, not in the paper -> tranform?
void printAction(struct Action *action){
   if (action != NULL){
      if (action->actiontype == SHUFFLE){
         printf("state %i ---> state %i: ", action->shuffle->fromState, action->shuffle->toState);
         printf("(shuffle {");
         for(int i = 0; i < action->shuffle->permSetSize; i++){
            printf("(");
            for(int j = 0; j < n; j++){
               printf("%i", action->shuffle->permutationSet[i*n+j]);
            }
            printf(")");
         }
         printf("})\n");
      } else if (action->actiontype == TURN){ // TURN
         printf("state %i ---> state %i: ", action->turn->fromState, action->turn->toState);
         printf("(turn {%i})  ", action->turn->turnPosition);
         for(int i = 0; i < n; i++){
            if(i == action->turn->turnPosition){
               printf("%i", action->turn->turnedCard);
            } else {
               printf("?");
            }
         }
         printf("\n");
      } else {
         printf("state %i ---> done\n ", action->result->fromState);
         printf("(result, %i, %i)\n", action->result->a, action->result->b);
      } 
   } else {
      printf("Error: could not print action, action is NULL\n");
   }

}

// Print state with all sequences and probabilities
void printState(struct State *state){
   printf("State index: %i\n", state->index);
   if(state != NULL){
      for(int i = 0; i < numberPossibleSequences; i++){ //was ist mit startstate?
         if(state->sequences[i] != NULL){
            printf("  ");
            if(state->sequences[i]->symbols != NULL){
               for (int j = 0; j < n; j++){
                  printf("%i", state->sequences[i]->symbols[j]);
               }
            }
            if(state->sequences[i]->nums != NULL && state->sequences[i]->dens != NULL){
               for (int j = 0; j < numberProbabilities; j++){
                  printf(" %i/%i", state->sequences[i]->nums[j], state->sequences[i]->dens[j]);
               }
               printf("\n");
            }
         } 
      }     
   }
}

// TODO: errorhandling -> addErrorMessage
// Parses value in permutationSet[X][Y]
int parsePermutationSetValue(cJSON *valueObject, int x, int y){
   setParsingStep(PARSE_PERMSETVALUE);

   if (currentAction != SHUFFLE){
      printf("Error in trace (parsePermutationSetValue): current action should be shuffle (%i), but is %i\n", SHUFFLE, currentAction);
      return CRITICAL_TRACE_ERROR;
   }
   int data = parseData(valueObject);
   if(data < 0){
      printf("Error parsing permutation Set (parsePermutationSetValue): data not valid  \n");
      return data;
   }

   /** 
    * Because a 'whole possible permutation set' of (possiblePermutations*n) occurences of 'permutationSet[X][Y]' in the trace 
    * are values BEFORE the actual permutationSet are stored in permutationSet, we need to ignore them.
    * On the first value in permutationSet after the assignment, the data structure for the permutationSet is created 
   */
   if(permutationSetPreAssign){
      if (permSetCounter < (numberPossiblePermutations*n)){
         permSetCounter++;
      } else {
         permutationSetPreAssign = false;

         int *newPermutationSet = malloc(sizeof(int)*permSetSize*n);
         if(!newPermutationSet){
            handleInternalError(BAD_MALLOC);
         } 

         newPermutationSet[x*n+y] = data;

         struct Action *newAction = malloc(sizeof(struct Action));
         struct Shuffle *shuffle = malloc(sizeof(struct Shuffle)); 
         if (!newAction || !shuffle){
            handleInternalError(BAD_MALLOC);
         }

         *shuffle = (struct Shuffle){stateFrom, currentStateIndex+1, permSetSize, newPermutationSet};
         *newAction = (struct Action){.actiontype = SHUFFLE, .shuffle = shuffle};
         actions[currentStateIndex] = newAction;
      }

   // Store the data
   } else {

      // TODO: permutation is stored like in code, not in paper -> fix this?
      actions[currentStateIndex]->shuffle->permutationSet[x*n+y] = data;

      // On the last value, set permutationSetPreAssign to true, because the next occurence of permutationSet in the trace will be before the assignment again
      if (x == (permSetSize-1) && y == (n-1)){
         permutationSetPreAssign = true;
         permSetCounter = 0;
         currentAction = -1; // reset currentAction
      }
   }
   return NO_ERROR;
}




cJSON* getNextObject(cJSON * object){

   char lastDataName[BUFFER_SIZE_SMALL];
   cJSON* lastName = cJSON_GetObjectItem(object, "name");

   cJSON* inObject = object;
   cJSON* outObject = object;
   while(outObject && !cJSON_IsArray(outObject)) {
      lastName = cJSON_GetObjectItem(outObject, "name");
      if(lastName && strcmp(lastName->valuestring, "array") != 0 && strcmp(lastName->valuestring, "struct")){
         strncpy(lastDataName, lastName->valuestring, strlen(lastName->valuestring)+1);
         //printf("!!! lastName is: %s\n", lastDataName);

      }

      outObject = cJSON_GetObjectItemCaseSensitive(inObject, "value");
      if(!outObject){
         outObject = cJSON_GetObjectItemCaseSensitive(inObject, "elements");
      } 
      if(!outObject){
        // printf("members\n");
         outObject = cJSON_GetObjectItemCaseSensitive(inObject, "members");
         // TODO: only when members? think about this
         // TODO: only probs???? think about this -> szenarien suchen, wo man in array muss, das länge 1 hat -> kann immer fälschlicherweise länge 1 haben!!!
         //if(outObject && cJSON_IsArray(outObject) && (cJSON_GetArraySize(outObject) == 1)){
         //   printf("NAME is: %s\n", lastDataName);
         //}
         if(outObject && cJSON_IsArray(outObject) && (cJSON_GetArraySize(outObject) == 1) && strcmp(lastDataName, "probs") == 0){
            outObject = cJSON_GetArrayItem(outObject, 0);
         }
      }

      // reached data value ("end of nested chain of objects")
      if(!outObject){
         if (cJSON_GetObjectItemCaseSensitive(inObject, "data") != NULL){
            return inObject;
         }
      }

      if(!outObject){
         return NULL;
      }
      inObject = outObject;
   } 

   return outObject;
}

int parseFraction(cJSON *sequenceObject, struct Sequence *newSequence, int *possible){
   setParsingStep(PARSE_FRACTION);

   // Get JSON array for probabilities
   cJSON *probsArray = getNextObject(cJSON_GetArrayItem(sequenceObject, 1));

   if(!probsArray){
      addErrorMessage(false, -1, -1, NULL);
      return DATA_NOT_VALID;
   }

   int sizeProbsArray = cJSON_GetArraySize(probsArray);
   if (sizeProbsArray != numberProbabilities) {
      addErrorMessage(true, sizeProbsArray, -1, NULL);
      return TRACE_ERROR;
   }

   // Parse fractions
   cJSON *fraction;
   int *newNums = malloc(numberProbabilities*sizeof(int));
   int *newDens = malloc(numberProbabilities*sizeof(int));
   if(!newNums || !newDens){
      handleInternalError(BAD_MALLOC);
   }

   currentFraction = 0;
   cJSON_ArrayForEach(fraction, probsArray) {

      cJSON *fractionMembers = getNextObject(fraction);
      if(!fractionMembers){
         addErrorMessage(false, -1, -1, NULL);
         return DATA_NOT_VALID;
      }

      // Parse numerator and denominator
      // The array in the JSON-Object should contain exactly two elements (numerator and denominator)
      int sizeFractionMembers = cJSON_GetArraySize(fractionMembers);
      if (sizeFractionMembers != 2){
         addErrorMessage(true, sizeFractionMembers, -1, NULL);
         return TRACE_ERROR;
      }
      cJSON *num = cJSON_GetArrayItem(fractionMembers, 0);
      cJSON *den = cJSON_GetArrayItem(fractionMembers, 1);
      if (!num || !den){
         addErrorMessage(false, -1, 2, NULL);
         return DATA_NOT_VALID;
      }

      // TODO change parseData
      // TODO: ignore different values of third parameter of addErrorMessage?
      // Store numerator and denominator
      int numVal = parseData(cJSON_GetObjectItemCaseSensitive(num, "value"));
      if(numVal < 0){
         addErrorMessage(false, -1, 0, NULL);
         return numVal;  // Data is invalid
      }
      newNums[currentFraction] = numVal;
      *possible |= numVal; 
  
      int denVal = parseData(cJSON_GetObjectItemCaseSensitive(den, "value"));
      if(denVal < 0){
         addErrorMessage(false, -1, 1, NULL);
         return denVal;  // Data is invalid
      }
      newDens[currentFraction] = denVal;
      currentFraction++;
   }

   if(possible){
      newSequence->nums = newNums;
      newSequence->dens = newDens;
   } else {  // If the sequence is not possible, free the memory for fractions and set the value in the state to NULL
      free(newNums);
      free(newDens);
   }
   currentFraction = -1;
   return NO_ERROR;
}


int parseSymbols(cJSON *sequenceObject, struct Sequence *newSequence){
   setParsingStep(PARSE_SYMBOLS);

   // Parse json array for symbols (first member of sequence object) and get symbols in the sequence
   cJSON *symbolValueElements = getNextObject(cJSON_GetArrayItem(sequenceObject, 0));
   if(!symbolValueElements){
      addErrorMessage(false, -1, -1, NULL);
      return DATA_NOT_VALID;
   }

   int sizeSymbolValueElements = cJSON_GetArraySize(symbolValueElements);
   if(sizeSymbolValueElements != n){
      addErrorMessage(true, sizeSymbolValueElements, -1, NULL);
      return TRACE_ERROR;
   }

   // Get each symbol in a sequence
   cJSON *symbol;
   newSequence->symbols = malloc(sizeof(int)*n);
   if(!newSequence->symbols){
      handleInternalError(BAD_MALLOC);
   }
   currentSymbol = 0;
   cJSON_ArrayForEach(symbol, symbolValueElements) {
      // TODO: hier macht getNextObject noch Probleme!!! Hier weiter machen!!!
      cJSON *symbolValue = getNextObject(symbol);

      if(symbolValue){
         int val = parseData(symbolValue);
         if(val < 0){
            addErrorMessage(false, -1, currentSymbol, NULL);
            return val; // If an error occured
         }
         newSequence->symbols[currentSymbol] = val;

      } else {
         addErrorMessage(false, -1, currentSymbol, NULL);
         return DATA_NOT_VALID;
      }
      currentSymbol++;
   }
   currentSymbol = -1;
   return NO_ERROR;
}


// Parses state from nested json object into struct 
int parseState(cJSON *valueObject){
   setParsingStep(PARSE_STATE);
   currentSequence = -1;

   /** 
    * skipNextState is true if the previously parsed states came from possiblePostStates;
    * Then the next state is already parsed and stored in the states array, so we can skip it
   */
   if (skipNextState){
      skipNextState = 0;
      // Set stateFrom to the index of the State that is chosen after turn
      stateFrom = stateFrom+chosenTurnStateIdx+1;
      return NO_ERROR; 
   }

    /**
     * The first L states in the cbmc output are the same (i.e. the start state). Because we only need the first state, 
     * so as long as 'next' is zero, we skip parsing the next state. A value of 'next' greater than zero indicates that 
     * the output contain a new (i.e. different) state, so we update currentStateIndex and parse the state.
     */  
   if(next > 0){
      currentStateIndex++;
   }
   if(states[currentStateIndex] != NULL){  // Checke whether the start state is already parsed
      return NO_ERROR;
   }

   // Create array for sequences
   struct Sequence **newSequences = malloc(sizeof(struct Sequence*)*numberPossibleSequences);
   if (!newSequences){
      handleInternalError(BAD_MALLOC);
   }
   memset(newSequences, 0, sizeof(struct Sequence *) * numberPossibleSequences);  // To avoid uninitialised values

   // Get JSON object that contains all sequences
   cJSON *sequences = getNextObject(valueObject);

   if (!sequences){
      addErrorMessage(false, -1, -1, NULL); 
      return DATA_NOT_VALID;
   }

   // Iterate over sequences to extract symbols and probabilities
   cJSON *seq = NULL;
   currentSequence = 0;
   cJSON_ArrayForEach(seq, sequences) {

      // Get JSON object for sequence
      cJSON *sequenceObject =  getNextObject(seq);
      if(!sequenceObject){
         addErrorMessage(false, -1, -1, NULL); 
         return DATA_NOT_VALID;
      }

      // Assumption: the JSON-Object contains an array with two elements (card values, probabilites)
      int sizeSequenceArray = cJSON_GetArraySize(sequenceObject);
      if (sizeSequenceArray != 2){
         addErrorMessage(false, sizeSequenceArray, -1, NULL); 
         return DATA_NOT_VALID;
      }

      struct Sequence *newSequence = malloc(sizeof(struct Sequence));
      if(!newSequence){
         handleInternalError(BAD_MALLOC);
      }

      // The cbmc output contains possible and impossible sequences, so we need to ignore all sequences that are not possible
      int possible = false; 

      // Parse fraction
      if(parseFraction(sequenceObject, newSequence, &possible) < 0){
         // TODO error handling??
         return DATA_NOT_VALID;
      }

      // If the sequence is possible, parse symbols
      if(possible){
         if(parseSymbols(sequenceObject, newSequence) < 0){
            return DATA_NOT_VALID;
         }
         newSequences[currentSequence] = newSequence;

      } else {  // If the sequence is not possible, free the memory for fractions and set the value in the state to NULL
         newSequences[currentSequence] = NULL;
      }
      currentSequence++;
      resetParsingStep();
   }

   // Cerate and add state to the states array
   struct State *state = malloc(sizeof(struct State));
   if(!state){
      handleInternalError(BAD_MALLOC);
   }
   *state = (struct State){currentStateIndex, newSequences};
   states[currentStateIndex] = state;

   return NO_ERROR;
}


// Parses possible states after a turn
int parsePossiblePostStates(cJSON *valueObject){
   currentParsingStep = PARSE_PPS;
   if(currentAction != TURN){
      printf("Error in trace (parsePossiblePostStates): current action should be turn (%i), but is %i\n", TURN, currentAction);
      return TRACE_ERROR;
   }

   stateFrom = currentStateIndex;

   cJSON *possible_states = cJSON_GetObjectItem(valueObject, "elements");
   if(!possible_states || !cJSON_IsArray(possible_states)){
      printf("Error parsing possible states after turn (parsePossiblePostStates): data for possible states is missing or is not an array\n"); 
      return DATA_NOT_VALID;
   }

   // Check if number of observations is correct
   int numberPostStates = cJSON_GetArraySize(possible_states);
   if(numberPostStates > numSym || numberPostStates < 2){ 
      printf("Error in trace in possible states after turn (parsePossiblePostStates): expected %i states but got %i\n", numSym, numberPostStates); 
      return TRACE_ERROR;
   }


   // Parse each possible state in possiblePostStates
   int currentState = 0;
   cJSON *state;
   cJSON_ArrayForEach(state, possible_states) {

      // Get data for state (state and values for 'isUsed')
      cJSON *valueMembers = cJSON_GetObjectItem(cJSON_GetObjectItem(state, "value"), "members");
      if(!valueMembers || !cJSON_IsArray(valueMembers) || cJSON_GetArraySize(valueMembers) == 0){
         printf("Error parsing possible states after turn (parsePossiblePostStates), state %i: data for state is missing or is not an array\n", currentState); 
         return DATA_NOT_VALID;
      }

      // Get data for state without values vor 'isUsed'
      cJSON *memberValue = cJSON_GetObjectItem(cJSON_GetArrayItem(valueMembers, 0), "value");
      if(!memberValue){ 
         printf("Error parsing possible states after turn (parsePossiblePostStates), state %i: data for state is missing or is not an array\n", currentState); 
         return DATA_NOT_VALID;
      }

      // Parse the state
      int errorcode = parseState(memberValue);
      if (errorcode < 0){
         printf("Error parsing possible states after turn (parsePossiblePostStates), state %i\n", currentState); 
         return errorcode;
      }

      // Get the observed card from the first sequence in the state that is not NULL
      int currentObservation = -1;  

      // sollte nicht passieren, außer irgendwas bei parseState ist grob schief gegangen
      if(!states[currentStateIndex]){
         handleInternalError(BAD_MALLOC);
      }

      // check if turnPosition is invalid
      if (turnPosition >= n || turnPosition < 0){
         printf("Error parsing possible states after turn (parsePossiblePostStates), state %i: turnPosition is out of bounds\n", currentState); 
         return DATA_NOT_VALID;
      }

      for (int i = 0; i < numberPossibleSequences; i++){
         if(states[currentStateIndex]->sequences[i] != NULL){
            // TODO: turnPosition starts with 0 -> different to paper? -> fix?
            currentObservation = states[currentStateIndex]->sequences[i]->symbols[turnPosition]; 
            break;
         } 
         // If no state with onservation could be found (= state is broken?), return error
         if (i == numberPossibleSequences-1){
            return TRACE_ERROR; // TODO: is this stupid? siehe oben beim letzten BAD_MALLOC, 
         }
      }

      // Add turn action with turn position and observed card to the actions array
      struct Action *newAction = malloc(sizeof(struct Action));
      struct Turn *turn = malloc(sizeof(struct Turn)); 
      if(!newAction || !turn){
         handleInternalError(BAD_MALLOC);
      }
      *turn = (struct Turn){stateFrom, currentStateIndex, currentObservation, turnPosition};
      *newAction = (struct Action){.actiontype = TURN, .turn = turn};
      actions[currentStateIndex-1] = newAction;

      currentState++;
   }

   // Reset currentAction
   currentAction = -1;

   // One of the parsed states is identical to the state that comes next in the cbmc output, so the next state does not need to be parsed
   skipNextState = 1;   
   return NO_ERROR;
}


/**
 * Parses the values for the cards that encode the result and store them in the global array resultPosition
 * These values (i.e. a and b) get overwritten each time when isFinalState is called, but this is ok since only the last assignment is relevant
 */
int parseAB(char *name, cJSON *valueObject, cJSON *location){
   currentParsingStep = PARSE_AB;
   cJSON *function = cJSON_GetObjectItem(location, "function");
   if (!function){
      printf("Error parsing value %s (parseAB): could not parse function name\n", name); 
      return DATA_NOT_VALID;
   }

   // Parse only if a or b occur in "isFinalState"
   if((strcmp(function->valuestring, "isFinalState") == 0)){
      int val = parseData(valueObject); 
      if (val < 0){
         printf("Error parsing value %s (parseAB): data is invalid\n", name); 
         return DATA_NOT_VALID;
      }

      // Store values of a and b in resultPositions
      if(strncmp(name, "a", 1) == 0){
         resultPositions[0] = val;
      } else {
         resultPositions[1] = val;
      }
   }
   return NO_ERROR;
}

// Parse permSetSize
int parsePermSetSize(cJSON *valueObject, cJSON *location){
   currentParsingStep = PARSE_PERMSETSIZE;

   cJSON *function = cJSON_GetObjectItem(location, "function");
   if (!function){
      printf("Error parsing size of permutation set (parsePermSetSize): could not parse function name\n"); 
      return DATA_NOT_VALID;
   }
   if((strcmp(function->valuestring, "applyShuffle") == 0)){
      int val = parseData(valueObject); 
      if (val < 0){
         printf("Error parsing size of permutation set (parsePermSetSize): data is invalid\n"); 
         return DATA_NOT_VALID;
      }
      permSetSize = val;
   }
   return NO_ERROR;
}


// TODO: possible to avoid "redundant" code? 
// TODO: comment
int parseObject(cJSON *traceItem){
   cJSON *value = cJSON_GetObjectItemCaseSensitive(traceItem, "value");
   cJSON *location = cJSON_GetObjectItemCaseSensitive(traceItem, "sourceLocation");
   cJSON *lhsKey = cJSON_GetObjectItemCaseSensitive(traceItem, "lhs");
   char *lhs = lhsKey->valuestring;

   int errorcode = 0;

   //TODO: error handling if value does not exist? 
   //TODO: stupid to get sourceLocation twice? maybe function that checks sourceLocation, line etc before?

   // Parse object with position of the turned card
   if(strcmp(lhs, "turnPosition") == 0){
      turnPosition = parseData(value); 
      if (turnPosition < 0) {
         errorcode = turnPosition;
      }

   // Parse index ('next') where the next state in reachableStates is stored
   } else if (strcmp(lhs, "next") == 0) {
      int nextVal = parseData(value); 

      if (nextVal < 0) {
         errorcode = nextVal;
      } else if (nextVal > 0){ // TODO comment
         next = nextVal; // store 'next' globally
      } 

   // Parse values of variables a and b if they occur in the method "isFinalState"
   } else if(strcmp(lhs, "a") == 0 || (strcmp(lhs, "b") == 0)){ 
      errorcode = parseAB(lhs, value, location);

   // Parse value (code) for the current action
   } else if(strcmp(lhs, "action") == 0){
      currentAction = parseData(value); 

      if (currentAction < 0){
         errorcode = currentAction;
      } 

   // Parse possible states after turn
   } else if (strcmp(lhs, "possiblePostStates.states") == 0){
      errorcode = parsePossiblePostStates(value);

   // Parse the index of the state in possiblePostStates that is chosen after turn
   } else if (strcmp(lhs, "stateIdx") == 0){
      chosenTurnStateIdx = parseData(value);

      if (chosenTurnStateIdx < 0){
         errorcode = currentAction;
      } 

   // Parse the size of the current permutationSet
   }  else if (strcmp(lhs, "permSetSize") == 0) {
      errorcode = parsePermSetSize(value, location);

   // Parse states from reachableStates[X].seq
   } else {

      // Regex to check whether lhs has the form "reachableStates[X].seq" (including format specifiers) 
      int reti;
      regex_t regex;
      reti = regcomp( &regex, "^reachableStates\\[[0-9]+[[:alpha:]]*\\]\\.seq$", REG_EXTENDED);
      if (reti) {
         handleInternalError(BAD_REGEX);
      }
      reti = regexec(&regex, lhs, 0, NULL, 0);
      regfree(&regex);

      if (!reti) {
         // Check if format specifier is valid
         char fmt0[BUFFER_SIZE_SMALL] = {0};
         int stateNumber;
         if((sscanf(lhs, "reachableStates[%d%9[^]].seq", &stateNumber, fmt0)) == 0){
            printf("Error parsing %s: failed to parse string\n", lhs); 
            return DATA_NOT_VALID;
         }
         int fsp0 = checkFormatSpecifier(fmt0);
         if (fsp0 < 0){
            // TODO entfernen und testen
            printf("Error parsing %s: wrong format specifier in data (%s)\n", lhs, fmt0); 
            return DATA_NOT_VALID;
         }

         // Check whether the number of the state is the same as next
         if(next > 0 && stateNumber != next){
            printf("Error in trace: value of 'next' (%i) differs from number of the parsed state (%i)\n", next, stateNumber);
            return TRACE_ERROR;
         }

         // Parse the state
         errorcode = parseState(value);

      // Parse permutationSet
      } else { //TODO parse otpermutationSet[Xl][Yl]?) Handle if not l! see parseData

         // Regex to check whether lhs has the form "permutationSet[X][Y].seq" (including format specifiers) 
         reti = regcomp(&regex, "^permutationSet\\[[0-9]+[[:alpha:]]*\\]\\[[0-9]+[[:alpha:]]*\\]$", REG_EXTENDED);
         if (reti) {
            handleInternalError(BAD_REGEX);
         }
         reti = regexec(&regex, lhs, 0, NULL, 0);
         regfree(&regex);

         if (!reti) {
            // Check if format specifier is valid
            int x, y; 
            char fmt1[BUFFER_SIZE_SMALL] = {0}, fmt2[BUFFER_SIZE_SMALL] = {0};
            if((sscanf(lhs, "permutationSet[%d%9[^]]][%d%9[^]]]", &x, fmt1, &y, fmt2)) < 2){
               printf("Error TODO  "); //TODO: error message?
               return DATA_NOT_VALID;
            }
            int fsp1 = checkFormatSpecifier(fmt1);
            int fsp2 = checkFormatSpecifier(fmt2);
            if (fsp1 < 0 || fsp2 < 0){
               // TODO error message?
               return DATA_NOT_VALID;
            }
            errorcode = parsePermutationSetValue(value, x, y);
         } 
      } 
      // If the value of lhs is not one we were looking for, just do nothing
   }
   if(errorcode < 0){
      printf("Error parsing %s\n", lhs); 
   }
   return errorcode;
}

// Print states and actions 
void printStatesAndActions(){
   for(int i = 0; i < maxGraphSize; i++){
      if(states[i] != NULL){
         printState(states[i]);
      }
      if(actions[i] != NULL){
         printAction(actions[i]);
      }
   }
}


// TODO comment
// TODO!!!! write help function or similar
// how to run currently (example): 
// ./Parser twoCardProtocol_2026_10_07_15_29_41_CEST.out 4 4 2 24 6 2
// ./Parser filename l n numSym numberPossiblePermutations numberPossibleSequences numberProbabilities
int main(int argc, char* argv[]) {
   if(argc != 8){
      perror("Error: missing arguments!\n");

      return EXIT_FAILURE;
   }

   // Get N, L, NUM_SYM, NUMBER_POSSIBLE_PERMUTATIONS, NUMBER_POSSIBLE_PERMUTATIONS, NUMBER_PROBABILITIES 
   n = atoi(argv[3]);
   l = atoi(argv[2]);

   numSym = atoi(argv[4]);
   numberPossiblePermutations = atoi(argv[5]);
   numberPossibleSequences = atoi(argv[6]);
   int weak_security = atoi(argv[7]);
   if (weak_security == 2){
      numberProbabilities = 2;
   } else {
      numberProbabilities = 4;
   }

   if(!(n && l && numSym && numberPossiblePermutations && numberPossibleSequences && numberProbabilities)){
      printf("Error: arguments must be valid numbers.\n");
      return EXIT_FAILURE;
   }



   // The number of states (or actions) should not be larger than the protocol length times the number of symbols
   maxGraphSize = l*numSym;
   // Read data from file

   FILE *fp = fopen(argv[1], "r");

   if (!fp) {
      printf("Error: Unable to open the file.\n");
      return EXIT_FAILURE;
   }

   // Get size of the file 
   fseek(fp, 0L, SEEK_END);
   int sz = ftell(fp);

   // Read commented lines (beginning with '#') and JSON data in two different buffers
   char *jsonBuffer = malloc(sizeof(char) * (sz+1));          // TODO: calloc? somehow, valgrind complains about this
   char *commentsBuffer = malloc(sizeof(char) * BUFFER_SIZE); 

   rewind(fp); // set fp to start of the file again?

   char line[BUFFER_SIZE];
   char *jsonPtr = jsonBuffer;
   int lineLength = 0;

   char *commentPtr = commentsBuffer;

   while(fgets(line, BUFFER_SIZE, fp)) {

      lineLength = strlen(line);

      if(line[0] == '#'){
         strncpy(commentPtr, line, lineLength);
         commentPtr += lineLength;
      } else {
         strncpy(jsonPtr, line, lineLength);
         jsonPtr += lineLength;
      }
   }

   //int len = fread(jsonBuffer, sizeof(char), sz, fp);
   //jsonBuffer[len] = '\0'; // add nullpointer

   fclose(fp);
   //printf("Buffer:\n%s", commentsBuffer); //TODO: change to error handling

   // Parse JSON data
   cJSON *json = cJSON_Parse(jsonBuffer);
   if (!json) {
     const char *error_ptr = cJSON_GetErrorPtr();
     if (error_ptr) {
         printf("Syntax error in JSON immediately before\n: %s\n", error_ptr);  // Prints object where error occurs (might  be large!)
     }
     free(jsonBuffer);
     free(commentsBuffer);
     cJSON_Delete(json);
     return EXIT_FAILURE; 
   }

   if (!json) {
        printf("Error parsing JSON\n");
        cleanJSON(jsonBuffer, commentsBuffer, json);
        return EXIT_FAILURE;
    }

   // Access JSON data
   if(!cJSON_IsArray(json)){
      printf("Error: cbmc output is not a JSON array");
      return EXIT_FAILURE;
   }

   // Find item with result in JSON array
   cJSON *result = NULL;
   int ouputSize = cJSON_GetArraySize(json);
   for (int i = 0; i < ouputSize; i++){
      cJSON *item = cJSON_GetArrayItem(json, i);
      if(cJSON_GetObjectItemCaseSensitive(item, "result") != NULL){
         result = item;
         break;
      } else if (i == ouputSize){
         printf("Error: trace not found\n");
         cleanJSON(jsonBuffer, commentsBuffer, json);
         return EXIT_FAILURE;
      }
   }

   // Get version 
   cJSON *versionObject = cJSON_GetArrayItem(json, 0);
   cJSON *version;
   if(versionObject){
      version = cJSON_GetObjectItemCaseSensitive(versionObject, "program");
      if(!version){
         printf("Error: version not found");
         return EXIT_FAILURE;
      }
   }

   // Get result item in JSON array
   cJSON *resultItem = cJSON_GetObjectItemCaseSensitive(result, "result"); 
   if(!resultItem){
      printf("Error: Result not found\n");
      cleanJSON(jsonBuffer, commentsBuffer, json);
      return EXIT_FAILURE;
   } else if(cJSON_GetArraySize(resultItem) != 1) {
      printf("Error: Format of JSON output is different as expected\n");
      cleanJSON(jsonBuffer, commentsBuffer, json);
      return EXIT_FAILURE;   
   }

   // Check if trace exists and get trace
   cJSON *trace = cJSON_GetObjectItem(cJSON_GetArrayItem(resultItem, 0), "trace");

   if(!trace){
      printf("Trace does not exist\n");
      cleanJSON(jsonBuffer, commentsBuffer, json);

   } else {

      // Allocate memory for states and actions
      actions = malloc(maxGraphSize*sizeof(struct Action*));
      states = malloc(maxGraphSize*sizeof(struct State*));

      int errorCounter = 0;
      // Parse json objects
      cJSON *traceItem = NULL;
      cJSON_ArrayForEach(traceItem, trace){
         cJSON *elem = cJSON_GetObjectItemCaseSensitive(traceItem, "lhs");
         // If the object stores a variable assignment
         if(elem){   

            // Error handling if parsing object results in an error (data is invalid or there is an error in the trace)
            int errorcode = parseObject(traceItem);

            // If an error occured: print function and line (from C code) and object where the error occured
            if (errorcode != NO_ERROR){
               // TODO: is this really necessary?
               cJSON *sourceLocation = cJSON_GetObjectItemCaseSensitive(traceItem, "sourceLocation");
               if(sourceLocation){
                  cJSON *function =  cJSON_GetObjectItemCaseSensitive(sourceLocation, "function");
                  cJSON *line = cJSON_GetObjectItemCaseSensitive(sourceLocation, "line");

                  if(function && line && cJSON_IsString(line)){
                     printf("Error in parsing '%s' (Line %i), function '%s'\n", elem->valuestring, atoi(line->valuestring),  function->valuestring);
                  } else {
                     printf("Error in parsing '%s', location could not be identified\n", elem->valuestring);
                  }

               } else {
                  printf("Error in parsing '%s', location could not be identified\n", elem->valuestring);
               }

               //printf("Object:\n");
               //char *error_object = cJSON_Print(traceItem);
               //printf("%s\n", error_object);  
               // TODO: only works when errors are not "critical" -> think about aborting if critial error
               if(errorcode == CRITICAL_TRACE_ERROR){
                  //TODO Errorhandling
                  printf("CRIRICAL TRACE ERROR\n");
                  break;
               }
               printf("-------------------- Error %i --------------------\n", errorCounter);
               errorCounter++;
            } 
         }
      }

      // Add result "action" to the list of actions
      if(addResult() < 0){
         return EXIT_FAILURE;
      }

   }


   // TODO: think about missing meta info? timeout, timestamp, etc?
   printf("Version: %s\nN = %i, L = %i\nNUM_SYM = %i\nNUMBER_POSSIBLE_PERMUTATIONS = %i\nNUMBER_POSSIBLE_SEQUENCES = %i\nNUMBER_PROBABILITIES = %i\n\n", version->valuestring, n, l, numSym, numberPossiblePermutations, numberPossibleSequences, numberProbabilities);

   printStatesAndActions();

   cleanJSON(jsonBuffer, commentsBuffer, json);
   cleanStructs();

   return EXIT_SUCCESS;
}
