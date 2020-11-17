// Copyright (C) 2020 Michael Kirsten, Michael Schrempp, Alexander Koch

//    This program is free software; you can redistribute it and/or modify
//    it under the terms of the GNU General Public License as published by
//    the Free Software Foundation; either version 3 of the License, or
//    (at your option) any later version.

//    This program is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//    GNU General Public License for more details.

//    You should have received a copy of the GNU General Public License
//    along with this program; if not, <http://www.gnu.org/licenses/>.

#include <stdlib.h>
#include <stdint.h>
#include <assert.h>

unsigned int nondet_uint();
void __CPROVER_assume(int x);
void __CPROVER_assert(int x, char y[]);

#define assert2(x, y) __CPROVER_assert(x, y)
#define assume(x) __CPROVER_assume(x)

/**
 * Size of input sequence (number of cards including both commitments plus additional cards).
 */
#ifndef N
#define N 4
#endif

/**
 * Amount of distinguishable card symbols.
 */
#ifndef NUM_SYM
#define NUM_SYM 2
#endif


/**
 * Number of all cards used for commitments
 */
#ifndef COMMIT
#define COMMIT 4
#endif

/**
 * Protocol length.
 */
#ifndef L
#define L 5
#endif

/**
 * Amount of different action types allowed in protocol, excluding result action.
 */
#ifndef A
#define A 2
#endif

/**
 * Number assigned to turn action.
 */
#ifndef TURN
#define TURN 0
#endif

/**
 * Number assigned to shuffle action.
 */
#ifndef SHUFFLE
#define SHUFFLE 1
#endif

/**
 * Regarding possibilities for a sequence, we (only) consider
 * - 0: probabilistic security
 *      (exact possibilities for a sequence)
 * - 1: input possibilistic security (yes or no)
 *      (whether the sequence can belong to the specific input)
 * - 2: output possibilistic security (yes or no)
 *      (to which output the sequence can belong)
 */
#ifndef WEAK_SECURITY
#define WEAK_SECURITY 2
#endif

/**
 * We always had four input possibilities,
 * this is changed if we only consider output possibilistic security.
 * This variable is used for over-approximating loops such that
 * their unrolling bound can be statically determined.
 */
#if WEAK_SECURITY == 2
    #define NUMBER_PROBABILITIES 2
#else
    #define NUMBER_PROBABILITIES 4
#endif

/**
 * For two players inserting yes or no to a protocol,
 * there are four different possibilities how the protocol could start.
 * For more players or other scenarios this value has to be adapted.
 */
#ifndef NUMBER_START_SEQS
#define NUMBER_START_SEQS 4
#endif

/**
 * 1 is finite runtime, 0 is restart-free Las-Vegas.
 * NOTE: this feature is not implemented yet
 */
#ifndef FINITE_RUNTIME
#define FINITE_RUNTIME 0
#endif

/**
 * If set to 1, only closed protocols with closed shuffles will be searched.
 */
#ifndef CLOSED_PROTOCOL
#define CLOSED_PROTOCOL 0
#endif

/**
 * If set to 1, only protocols with random cuts will be searched.
 */
#ifndef FORCE_RANDOM_CUTS
#define FORCE_RANDOM_CUTS 0
#endif

/**
 * Maximum number of sequences (usually N!).
 * This value can be lowered if there are multiple indistinguishable symbols in the deck.
 * This variable is used for over-approximating loops such that
 * their unrolling bound can be statically determined.
 */
#ifndef NUMBER_POSSIBLE_SEQUENCES
#define NUMBER_POSSIBLE_SEQUENCES 24
#endif

/**
 * Maximum number of permutations fpr the given number of cards (N!).
 * This value has to be computed by our script, or adjusted manually.
 */
#ifndef NUMBER_POSSIBLE_PERMUTATIONS
#define NUMBER_POSSIBLE_PERMUTATIONS 24
#endif

/**
 * This variable is used to limit the permutation set in any shuffle.
 * This can reduce the running time of this program.
 * When reducing this Variable, keep in mind that it could exclude some valid protocols,
 * as some valid permutation sets are not longer considered.
 */
#ifndef MAX_PERM_SET_SIZE
#define MAX_PERM_SET_SIZE NUMBER_POSSIBLE_PERMUTATIONS
#endif

#ifndef SUBGROUP_SIZE_1
#define SUBGROUP_SIZE_1 1
#endif

#ifndef SUBGROUP_SIZE_2
#define SUBGROUP_SIZE_2 2
#endif

#ifndef SUBGROUP_SIZE_3
#define SUBGROUP_SIZE_3 3
#endif

#ifndef SUBGROUP_SIZE_4
#define SUBGROUP_SIZE_4 4
#endif

#ifndef SUBGROUP_SIZE_5
#define SUBGROUP_SIZE_5 5
#endif

#ifndef SUBGROUP_SIZE_6
#define SUBGROUP_SIZE_6 6
#endif

#ifndef SUBGROUP_SIZE_7
#define SUBGROUP_SIZE_7 8
#endif

#ifndef SUBGROUP_SIZE_8
#define SUBGROUP_SIZE_8 10
#endif

#ifndef SUBGROUP_SIZE_9
#define SUBGROUP_SIZE_9 12
#endif

#ifndef SUBGROUP_SIZE_10
#define SUBGROUP_SIZE_10 20
#endif

#ifndef SUBGROUP_SIZE_11
#define SUBGROUP_SIZE_11 24
#endif

#ifndef SUBGROUP_SIZE_12
#define SUBGROUP_SIZE_12 60
#endif

#ifndef SUBGROUP_SIZE_13
#define SUBGROUP_SIZE_13 120
#endif

#ifndef NUMBER_SUBGROUP_SIZES
#define NUMBER_SUBGROUP_SIZES 13
#endif

const unsigned int subgroupSizes[13] =
    { SUBGROUP_SIZE_1, SUBGROUP_SIZE_2, SUBGROUP_SIZE_3, SUBGROUP_SIZE_4, SUBGROUP_SIZE_5,
      SUBGROUP_SIZE_6, SUBGROUP_SIZE_7, SUBGROUP_SIZE_8, SUBGROUP_SIZE_9, SUBGROUP_SIZE_10,
      SUBGROUP_SIZE_11, SUBGROUP_SIZE_12, SUBGROUP_SIZE_13 };

/**
 * After a turn, the protocol tree splits up in one subtree for each possible observation.
 * You can use these two variables for restricting the number of observations after every turn.
 * In our case, we exclude the "trivial turn" where the turned card is already known since the
 * protocol would not branch there. Therefore we force the program to have at least two branches
 * after every turn operation.
 */
#ifndef MIN_TURN_OBSERVATIONS
#define MIN_TURN_OBSERVATIONS 2
#endif

/**
 * See description of MIN_TURN_OBSERVATIONS above.
 */
#ifndef MAX_TURN_OBSERVATIONS
#define MAX_TURN_OBSERVATIONS NUM_SYM
#endif

/**
 * The number of states stored in the protocol run (Start state + all L derived states).
 */
#ifndef MAX_REACHABLE_STATES
#define MAX_REACHABLE_STATES L+1
#endif

struct fraction {
    unsigned int num; // The numerator.
    unsigned int den; // The denominator.
};

struct fractions {
    struct fraction frac[NUMBER_PROBABILITIES];
};

/**
 * This is one sequence, as seen from left to right.
 *
 * If the sequence can belong to a specific input sequence,
 * then the probabilities entry is set to the probability for this input sequence.
 * Indices:
 * - 0: X_00
 * - 1: X_01
 * - 2: X_10
 * - 3: X_11
 *
 * If the sequence is not contained in the state, all probabilities are set to zero.
 *
 * We save the probabilities as numerator/denominator (of type fraction),
 * so we can avoid floating point operations and divisions.
 *
 * One line looks like this:
 *   val:           [card#1][card#2]..[card#N]
 *   probs:         [num#1]..[num#4]
 *   (num./denom.)  [den#1]..[den#4]
 *
 * For input-possibilistic protocols,
 * we only need to determine whether a sequence can belong to a specific input:
 *    [card#1][card#2]..[card#N]
 *    [bool#1]..[bool#4]
 *
 * For output-possibilistic protocols,
 * we only need to determine whether a sequence can belong to a specific output:
 *    [card#1][card#2]..[card#N]
 *    [bool#1][bool#2]
 * Note that in this scenario, we have bool#1 == X_0 and bool#2 == X_1.
 */
struct sequence {
    unsigned int val[N];
    struct fractions probs;
};


/**
 * All sequences are remembered here, as seen from left to right, sorted alphabetically.
 * The states in this program are equal to the states in KWH trees.
 */
struct state {
    struct sequence seq[NUMBER_POSSIBLE_SEQUENCES];
};

/**
 * All permutations are remembered here, as seen from left to right, sorted alphabetically.
 */
struct permutationState {
    struct sequence seq[NUMBER_POSSIBLE_PERMUTATIONS];
};

/**
 * We use this struct to return arrays of states after turn operations.
 * There is one state for each possible observation.
 * In each turn, each sequence with an observable card #X is stored in
 * state X-1 and moreover isUsed[X-1] == 1 holds.
 * If a card Y cannot be observed in the turn operation, then isUsed[Y-1] == 0 must hold.
 */
struct turnStates {
    struct state states[MAX_TURN_OBSERVATIONS];
    unsigned int isUsed[MAX_TURN_OBSERVATIONS];
};

/**
 * An integer array with length N.
 */
struct narray {
    unsigned int arr[N];
};

/**
 * An integer array with length NUM_SYM.
 */
struct numsymarray {
    unsigned int arr[NUM_SYM];
};

/**
 * One bit is represented by two cards, a and b.
 * If the first card is lower than the second card, the bit represents the value "0"
 * If the first card is higher than the second card, the bit represents the value "1"
 * Note that if both cards are equal, the bit is "undefined".
 * This must not happen in our implementation, but must be considered for multiple
 * indistinguishable cards.
 */
unsigned int isZero(unsigned int a, unsigned int b) {
    return a < b;
}

/**
 * See description of isZero(uint, uint) above.
 */
unsigned int isOne(unsigned int a, unsigned int b) {
    return a > b;
}

/**
 * Constructor for states. Only use this to create new states.
 */
struct state getEmptyState() {
    struct state s;
    struct numsymarray symbolCount;
    for (unsigned int i = 0; i < NUM_SYM; i++) {
        symbolCount.arr[i] = 0;
    }

    for (unsigned int i = 0; i < NUMBER_POSSIBLE_SEQUENCES; i++) {
        struct numsymarray taken;
        for (unsigned int j = 0; j < NUM_SYM; j++) {
            taken.arr[j] = 0;
        }
        for (unsigned int j = 0; j < N; j++) {
            s.seq[i].val[j] = nondet_uint();
            unsigned int val = s.seq[i].val[j];
            assume (0 < val  && val <= NUM_SYM);
            unsigned int idx = val - 1;
            taken.arr[idx]++;
            assume (taken.arr[idx] <= N-2); // At least two symbols have to be different. Players cannot commit otherwise.
        }
        for (unsigned int  j = 0; j < NUM_SYM; j++) {
            if(i == 0) {
                symbolCount.arr[j] = taken.arr[j];
            } else { // We ensure that every sequence consists of the same symbols
                assume(taken.arr[j] == symbolCount.arr[j]);
            }
        }

        // Here we store the numerators and denominators
        for (unsigned int j = 0; j < NUMBER_PROBABILITIES; j++) {
            s.seq[i].probs.frac[j].num = 0;
            s.seq[i].probs.frac[j].den = 1;
        }
    }

    for (unsigned int i = 1; i < NUMBER_POSSIBLE_SEQUENCES; i++) {
        unsigned int checked = 0;
        unsigned int last = i - 1;
        for (unsigned int j = 0; j < N; j++) {
            // Check lexicographic order
            unsigned int a = s.seq[last].val[j];
            unsigned int f = s.seq[i].val[j];
            checked |= (a < f);
            assume (checked || a == f);
        }
        assume (checked);
    }
    return s;
}

/**
 * We store one empty state at beginning of the program to save ressources.
 */
struct state emptyState;

/**
 * We store all possible permutations into a seperate state to save resources.
 */
struct permutationState stateWithAllPermutations;

/**
 * This method constructs the start sequence for a given commitment length COMMIT
 * using nodeterministic assignments. We only consider the case where Alice uses
 * the cards "1" and "2", and Bob uses the cards "3" and "4".
 */
struct narray getStartSequence() {
    assume (N >= COMMIT); // We assume at least as many cards as needed for the commitments.
    struct numsymarray taken;
    for (unsigned int i = 0; i < NUM_SYM; i++) {
        taken.arr[i] = 0;
    }
    struct narray res;
    for (unsigned int i = 0; i < COMMIT; i++) {
        res.arr[i] = nondet_uint();
        unsigned int val = res.arr[i];
        assume (0 < val && val <= COMMIT && val <= NUM_SYM);
        unsigned int idx = val - 1;
        assume (taken.arr[idx] < COMMIT / NUM_SYM);
        taken.arr[idx]++;
    }
    // Here we assume that each player only uses fully distinguishable cards
    assume (res.arr[1] != res.arr[0]);
    assume (res.arr[3] != res.arr[2]);
    for (unsigned int i = COMMIT; i < N; i++) {
        res.arr[i] = nondet_uint();
        assume (0 < res.arr[i]);
        assume (res.arr[i] <= NUM_SYM);
    }
    return res;
}

/**
 * Determines whether the sequence belongs to at least one input sequence.
 * This value is true iff the sequence could be generated from any of the protocol's
 * input sequeces through the currently executed actions.
 */
unsigned int isStillPossible(struct fractions probs) {
    unsigned int res = 0;
    for (unsigned int i = 0; i < NUMBER_PROBABILITIES; i++) {
        res |= probs.frac[i].num;
    }
    return res;
}

/**
 * Given an array containing a sequence, we return the index of the given sequence in a state.
 */
unsigned int getSequenceIndexFromArray(struct narray compare, struct state compareState) {
    unsigned int seqIdx = nondet_uint();
    assume (seqIdx < NUMBER_POSSIBLE_SEQUENCES);
    struct sequence seq = compareState.seq[seqIdx];

    for (unsigned int i = 0; i < N; i++) {
        assume (compare.arr[i] == seq.val[i]);
    }
    return seqIdx;
}

struct permutationState getStateWithAllPermutations() {
 struct permutationState s;
    for (unsigned int i = 0; i < NUMBER_POSSIBLE_PERMUTATIONS; i++) {
        struct narray taken;
        for (unsigned int j = 0; j < N; j++) {
            taken.arr[j] = 0;
        }
        for (unsigned int j = 0; j < N; j++) {
            s.seq[i].val[j] = nondet_uint();
            unsigned int val = s.seq[i].val[j];
            assume (0 < val && val <= N);
            unsigned int idx = val - 1;
            assume (!taken.arr[idx]);
            taken.arr[idx]++;
        }
    }

    // Not needed, but to avoid state space explosion
    for (unsigned int i = 0; i < NUMBER_POSSIBLE_PERMUTATIONS; i++) {
        for (unsigned int j = 0; j < NUMBER_PROBABILITIES; j++) {
            s.seq[i].probs.frac[j].num = 0;
            s.seq[i].probs.frac[j].den = 1;
        }
    }

    for (unsigned int i = 1; i < NUMBER_POSSIBLE_PERMUTATIONS; i++) {
        unsigned int checked = 0;
        unsigned int last = i - 1;
        for (unsigned int j = 0; j < N; j++) {
            // Check lexicographic order
            unsigned int a = s.seq[last].val[j];
            unsigned int f = s.seq[i].val[j];
            checked |= (a < f);
            assume (checked || a == f);
        }
        assume (checked);
    }
    return s;
}

/**
 * Calculates the resulting permutation when we first apply firstPermutation to a sequence, and
 * subsequently we apply secondPermutation (secondPermutation ° firstPermutation).
 */
struct narray combinePermutations(struct narray firstPermutation,
                                  struct narray secondPermutation) {
     struct narray result = { .arr = { 0 } };
     for (unsigned int i = 0; i < N; i++) {
         result.arr[firstPermutation.arr[i]] = secondPermutation.arr[i];
     }
     return result;
}

/**
 * Check if the sequence is a bottom sequence (belongs to more than one possible output).
 */
unsigned int isBottom(struct fractions probs) {
    unsigned int bottom = 0;

    if (WEAK_SECURITY == 2) {
        bottom = probs.frac[0].num && probs.frac[1].num;
    } else {
        bottom = (probs.frac[0].num || probs.frac[1].num || probs.frac[2].num) && probs.frac[3].num;
    }
    return bottom;
}

/**
 * Check a state for bottom sequences.
 */
unsigned int isBottomFree(struct state s) {
    unsigned int res = 1;
    unsigned int done = 0;
    for (unsigned int i = 0; i < NUMBER_POSSIBLE_SEQUENCES; i++) {
        if (!done && isBottom(s.seq[i].probs)) {
            done = 1;
            res = 0;
        }
    }

    return res;
}

/**
 * Checks whether a state neither contains bottom sequences nor excludes inputs.
 * A bottom sequence refers to the output 0 and 1.
 * A state excludes inputs if there is no sequence in the state which could
 * belong to this input. Both options would lead to a state in which we could
 * not continue with the protocol and therefore we would need to do a restart.
 * These states are not valid in our setup and therefore they should not be
 * included in a protocol.
 */
unsigned int isValid(struct state s) {
    unsigned int res = isBottomFree(s);

    // Check whether every input is possible.
    for (unsigned int k = 0; k < NUMBER_PROBABILITIES; k++) {
        unsigned int seqIndexForThisProbability = nondet_uint();
        assume (seqIndexForThisProbability < NUMBER_POSSIBLE_SEQUENCES);
        struct sequence seq = s.seq[seqIndexForThisProbability];

        /*
         * Now nondeterministic: We choose only sequences with probability > 0
         * Cut the trace if we need to find a protocol from a non-valid state.
         */
        assume (seq.probs.frac[k].num);
    }

    return res;
}

/**
 * Checks whether the state contains two columns that encode a valid result bit.
 */
unsigned int isFinalState(struct state s) {
    unsigned int res = 0;

    if (isValid(s)) { // Non-valid states cannot be final.
        res = 1;
        /**
         * Check nondeterministically whether there are two columns encoding the result bit
         * (they need to have only two symbols, as otherwise we may be able to get information
         * from the output basis of the result bit).
         */
        unsigned int a = nondet_uint(); // Index of the first card.
        unsigned int b = nondet_uint(); // Index of the second card.

        assume (a < N && b < N && a != b);
        unsigned int lowerCard = 0;
        unsigned int higherCard = 0;

        unsigned int done = 0;
        for (unsigned int i = 0; i < NUMBER_POSSIBLE_SEQUENCES; i++) {
            if (!done && isStillPossible(s.seq[i].probs)) {
                // IF XOR, SOMETHING LIKE THIS: 2 || 3
                unsigned int deciding = s.seq[i].probs.frac[NUMBER_PROBABILITIES - 1].num;
                unsigned int first = s.seq[i].val[a];
                unsigned int second = s.seq[i].val[b];
                assume (first != second);
                if (!higherCard && !lowerCard) {
                    // In a 1-sequence, the first card is higher, otherwise the second one.
                    higherCard = deciding ? first : second;
                    lowerCard = deciding ? second : first;
                } else {
                    /**
                     * Check whether for each 1-sequence, there is first the higher card AND
                     * for each 0-sequence, there is first the lower card. Also check whether
                     * there are only two cards used as output basis in this state.
                     */
                    if (   (deciding
                            && !(   first == higherCard
                                 && second == lowerCard))
                        || (!deciding
                            && !(   second == higherCard
                                 && first == lowerCard))) {
                        done = 1;
                        res = 0;
                    }
                }
            }
        }
    }
    return res;
}

/**
 * Check a permutation set whether it is closed under transitivity.
 */
void checkTransitivityOfPermutation(unsigned int permutationSet[MAX_PERM_SET_SIZE][N],
                                    unsigned int permSetSize) {
    unsigned int onlyPerm = (permSetSize == 1);

    if (FORCE_RANDOM_CUTS && !onlyPerm) {
        unsigned int onlyRandomCuts = 1;
        unsigned int cntStaysFix = 0;

        for (unsigned int i = 0; i < MAX_PERM_SET_SIZE; i++) {
            if (i < permSetSize) {
                unsigned int staysFix[N] = { 0 };
                unsigned int hasStayFix = 0;
                unsigned int lastNotFix = N;
                for (unsigned int j = 0; j < N; j++) {
                    if (j < permSetSize) {
                        staysFix[j] = (permutationSet[i][j] == j);
                    }
                    hasStayFix |= staysFix[j];
                    lastNotFix = staysFix[j] ? lastNotFix : j;
                }
                cntStaysFix += hasStayFix;

                unsigned int prev = N - 1;
                for (unsigned int j = 0; j < N; j++) {
                    unsigned int p = permutationSet[i][prev];
                    unsigned int c = permutationSet[i][j];
                    if (!staysFix[j]) {
                        onlyRandomCuts &= ((p < c) || ((p == lastNotFix) && (c == 0)));
                        prev = j;
                    }
                }
            }
        }
        onlyRandomCuts &= (cntStaysFix == permSetSize);
        assume (onlyRandomCuts);
    }

    if (!onlyPerm) {
        unsigned int permittedSoubgroupSize = 0;
        for (unsigned int i = 0; i < NUMBER_SUBGROUP_SIZES; i++) {
            permittedSoubgroupSize |= (permSetSize == subgroupSizes[i]);
        }
        assume ((5 < N) || permittedSoubgroupSize);

        // hier hin der check, ob permSetSize eine Größe aus der obigen Liste hat
        for (unsigned int i = 0; i < MAX_PERM_SET_SIZE; i++) {
            if (i < permSetSize) {
                for (unsigned int j = 0; j < MAX_PERM_SET_SIZE; j++) {
                    if (j < permSetSize) {
                        /**
                         * For every pair of permutations, check if the permutation that results
                         * from combining both permutations is contained in the permutation set.
                         * The resulting permutation is determined nondeterministically. The
                         * variables i and j are used to iterate over all permutations in the
                         * permutationSet. In fact this is a check for transitivity.
                         */
                        unsigned int resultIdx = nondet_uint();
                        assume (resultIdx < permSetSize);
                        struct narray firstPermutation  = { .arr = { 0 } };
                        struct narray secondPermutation = { .arr = { 0 } };

                        for (unsigned int k = 0; k < N; k++) {
                            firstPermutation.arr[k]  = permutationSet[i][k];
                            secondPermutation.arr[k] = permutationSet[j][k];
                        }

                        struct narray permResultFromBothPerms =
                            combinePermutations(firstPermutation, secondPermutation);
                        for (unsigned int k = 0; k < N; k++) {
                            assume (   permResultFromBothPerms.arr[k]
                                    == permutationSet[resultIdx][k]);
                        }
                    }
                }
            }
        }
    }
}

/**
 * Update the possibilities of a sequence after a shuffle.
 */
struct fractions recalculatePossibilities(struct fractions probs,
                                          struct fractions resProbs,
                                          unsigned int permSetSize) {
    for (unsigned int k = 0; k < NUMBER_PROBABILITIES; k++) {
        struct fraction prob = probs.frac[k];
        unsigned int num   = prob.num;
        unsigned int denom = prob.den;

        if (num && WEAK_SECURITY) {
            resProbs.frac[k].num |= num;
        } else if (num) {
            /**
             * Only update fractions in case we are in the
             * strong security setup.
             */
            // Update denominator.
            resProbs.frac[k].den = denom * permSetSize;
            // Update numerator.
            resProbs.frac[k].num = (num * permSetSize) + denom;
        }
    }
    return resProbs;
}

/**
 * Calculate the state after a shuffle operation starting from s with the given permutation set.
 */
struct state doShuffle(struct state s,
                       unsigned int permutationSet[MAX_PERM_SET_SIZE][N],
                       unsigned int permSetSize) {
    struct state res = emptyState;
    // For every sequence in the input state.
    for (unsigned int i = 0; i < NUMBER_POSSIBLE_SEQUENCES; i++) {
        if (isStillPossible(s.seq[i].probs)) {
            // For every permutation in the permutation set.
            for (unsigned int j = 0; j < MAX_PERM_SET_SIZE; j++) {
                if (j < permSetSize) {
                    struct narray resultingSeq = { .arr = { 0 } };
                    for (unsigned int k = 0; k < N; k++) {
                        // Apply permutation j to sequence i.
                        resultingSeq.arr[permutationSet[j][k]] = s.seq[i].val[k];
                    }
                    unsigned int resultSeqIndex = // Get the index of the resulting sequence.
                        getSequenceIndexFromArray(resultingSeq, res);
                    // Recalculate possibilities.
                    res.seq[resultSeqIndex].probs =
                        recalculatePossibilities(s.seq[i].probs,
                                                 res.seq[resultSeqIndex].probs,
                                                 permSetSize);
                }
            }
        }
    }
    return res;
}

/**
 * Generate a nondeterministic permutation set and apply it to the given state.
 */
struct state applyShuffle(struct state s) {
    // Generate permutation set (shuffles are assumed to be uniformly distributed).
    unsigned int permSetSize = nondet_uint();
    assume (0 < permSetSize && permSetSize <= MAX_PERM_SET_SIZE);

    unsigned int permutationSet[MAX_PERM_SET_SIZE][N] = { 0 };
    unsigned int takenPermutations[NUMBER_POSSIBLE_PERMUTATIONS] = { 0 };
    /**
     * Choose permSetSize permutations nondeterministically. To achieve this,
     * generate a nondeterministic permutation index and get the permutation from this index.
     * No permutation can be chosen multiple times.
     */
    unsigned int lastChosenPermutationIndex = 0;
    for (unsigned int i = 0; i < MAX_PERM_SET_SIZE; i++) {
        if (i < permSetSize) { // Only generate permutations up to permSetSize.
            unsigned int permIndex = nondet_uint();
            // This ensures that the permutation sets are sorted lexicographically.
            assume (lastChosenPermutationIndex <= permIndex);
            assume (permIndex < NUMBER_POSSIBLE_PERMUTATIONS);
            assume (!takenPermutations[permIndex]);

            takenPermutations[permIndex] = 1;
            lastChosenPermutationIndex = permIndex;

            for (unsigned int j = 0; j < N; j++) {
                permutationSet[i][j] = stateWithAllPermutations.seq[permIndex].val[j] - 1;
                /**
                 * The '-1' is important. Later, we convert to array indices such as
                 * array[permutationSet[x][y]]. Without the '-1', we would get out-
                 * of-bound errors there.
                 */
            }
        }
    }

    if (CLOSED_PROTOCOL || FORCE_RANDOM_CUTS) { // Check for closedness.
        checkTransitivityOfPermutation(permutationSet, permSetSize);
        // As in state trees, we want to include the identity if it is not a permutation.
        assume (permSetSize == 1 || takenPermutations[0] > 0);
    }
    // Apply the shuffle that was generated above.
    struct state res = doShuffle(s, permutationSet, permSetSize);

    assume (isBottomFree(res));
    return res;
}

struct turnStates alignAndAssignFractions(struct turnStates result,
                                          struct fractions probs) {
    for (unsigned int i = 0; i < MAX_TURN_OBSERVATIONS; i++) {
        if (result.isUsed[i]) {
            unsigned int newDenominator = 1;
            /**
             * Align all fractions to the same denominator,
             * such that the sum of all fractions is again == 1.
             * This denominator is not yet stored in the arrays,
             * since we might need the old denominators later-on to reduce the fractions!
             */
            for (unsigned int j = 0; j < NUMBER_PROBABILITIES; j++) {
                for (unsigned int k = 0; k < NUMBER_PROBABILITIES; k++) {
                    if (k != j) {
                        probs.frac[j].num *= probs.frac[k].den;
                    }
                }
                // Only accept states with equal possibilities.
                assume (probs.frac[j].num == probs.frac[0].num);
                newDenominator *= probs.frac[j].den;
            }
            // Update fractions in result state.
            for (unsigned int j = 0; j < NUMBER_POSSIBLE_SEQUENCES; j++) {
                for (unsigned int k = 0; k < NUMBER_PROBABILITIES; k++) {
                    result.states[i].seq[j].probs.frac[k].num *= newDenominator;
                    result.states[i].seq[j].probs.frac[k].den *= probs.frac[k].num;
                }
            }
        }
    }
    return result;
}

struct fractions computeTurnProbabilities(struct turnStates result) {
    struct fractions probs;
    for (unsigned int i = 0; i < NUMBER_PROBABILITIES; i++) {
        probs.frac[i].num = 0;
        // We later want to multiply all denominators with each other.
        probs.frac[i].den = 1;
    }
    for (unsigned int i = 0; i < MAX_TURN_OBSERVATIONS; i++) {
        if (result.isUsed[i]) { // Only recalculate states that are used later.
            struct state resultState = result.states[i];
            // Add up all possibilities in a state.
            for (unsigned int j = 0; j < NUMBER_POSSIBLE_SEQUENCES; j++) {
                struct sequence resultSeq = resultState.seq[j];
                if (isStillPossible(resultSeq.probs)) {
                    for (unsigned int k = 0; k < NUMBER_PROBABILITIES; k++) {
                        struct fraction prob = resultSeq.probs.frac[k];
                        unsigned int num   = prob.num;
                        unsigned int denom = prob.den;
                        unsigned int newNum   = probs.frac[k].num;
                        unsigned int newDenom = probs.frac[k].den;
                        /**
                         * If the sequence does not belong to an input sequence,
                         * this sequence should not be updated in this step.
                         */
                        if (num && denom == newDenom) {
                            probs.frac[k].num += num;
                        } else if (num && denom != newDenom) {
                            probs.frac[k].num = (newNum * denom) + (num * newDenom);
                            probs.frac[k].den *= denom;
                        }
                    }
                }
            }
        }
    }
    return probs;
}

/**
 * Given state and the position of a turned card,
 * this function returns all branched states resulting from the turn.
 */
struct turnStates copyObservations(struct state s, unsigned int turnPosition) {
    struct turnStates result;
    // Initialise N empty states.
    for (unsigned int i = 0; i < MAX_TURN_OBSERVATIONS; i++) {
        result.states[i] = emptyState;
        result.isUsed[i] = 0;
    }
    unsigned int cntTurnObservations = 0;
    /**
     * If a sequence belongs to an observation X, then copy this
     * sequence into the state of observation X.
     */
    for (unsigned int i = 0; i < NUMBER_POSSIBLE_SEQUENCES; i++) {
        struct sequence seq = s.seq[i];
        if (isStillPossible(seq.probs)) {
            unsigned int turnedCardNumber = seq.val[turnPosition];
            unsigned int turnIdx = turnedCardNumber - 1;
            cntTurnObservations += result.isUsed[turnIdx] ? 0 : 1;
            result.isUsed[turnIdx] = 1;
            assume (cntTurnObservations <= MAX_TURN_OBSERVATIONS);
            for (unsigned int j = 0; j < NUMBER_PROBABILITIES; j++) {
                struct fraction prob = seq.probs.frac[j];
                // Copy numerator.
                result.states[turnIdx].seq[i].probs.frac[j].num = prob.num;
                if (!WEAK_SECURITY) { // Probabilistic security
                    // Copy denominator.
                    result.states[turnIdx].seq[i].probs.frac[j].den = prob.den;
                }
            }
        }
    }
    assume (MIN_TURN_OBSERVATIONS <= cntTurnObservations);
    return result;
}

/**
 * Turn at a nondeterministic position and return all resulting states. For each possible
 * observation, there is a distinct state. If an observation cannot occur through this
 * turn operation, the according isUsed entry is set to zero. For more information, refer
 * to the documentation of "turnStates".
 */
struct turnStates applyTurn(struct state s) {
    // Choose turn position nondeterministically, otherwise we cannot do two turns in a row.
    unsigned int turnPosition = nondet_uint();
    assume (turnPosition < N);

    struct turnStates result = copyObservations(s, turnPosition);
    if (WEAK_SECURITY) { // Weaker security check: output-possibilistic or input-possibilistic.
        for (unsigned int stateNumber = 0; stateNumber < MAX_TURN_OBSERVATIONS; stateNumber++) {
            if (result.isUsed[stateNumber]) {
                struct state resultState = result.states[stateNumber];
                // Now nondeterministic. We only need to find one sequence for
                // every possible in-/output. We assume nondeterministically
                // that the state contains a sequence for every in-/output possibility.
                for (unsigned int i = 0; i < NUMBER_PROBABILITIES; i++) {
                    unsigned int seqIndex = nondet_uint();
                    assume (seqIndex < NUMBER_POSSIBLE_SEQUENCES);
                    assume (resultState.seq[seqIndex].probs.frac[i].num);
                }
            }
        }
    } else { // Probabilistic security.
        struct fractions probs = computeTurnProbabilities(result);
        result = alignAndAssignFractions(result, probs);
    }

    return result;
}

/**
 * Apply L nondeterministic actions (excluding the result action).
 * The function evaluates to true if:
 *   - We find a finite state in the restart-free setting.
 *   - All remaining states are finite in the finite-runtime setting.
 */
unsigned int performActions(struct state s) {
    unsigned int result = 0;

    // All reachable states are stored here.
    struct state reachableStates[MAX_REACHABLE_STATES];
    for (unsigned int i = 0; i < MAX_REACHABLE_STATES; i++) {
        // Begin calculation from start state.
        reachableStates[i] = s;
    }

    for (unsigned int i = 0; i < L; i++) {
        // Choose the action nondeterministically.
        unsigned int action = nondet_uint();
        assume (action < A);
        // If A is greater than 2, we must add cases for additional actions below.
        assume (A == 2);
        unsigned int next = i + 1;

        if (action == TURN) {
            /**
             * Generate N states through a turn operation and store them in the
             * reachableStates array. For every used state, we get another path
             * in the protocol that must be processed.
             */
            struct turnStates possiblePostStates = applyTurn(reachableStates[i]);

            unsigned int stateIdx = nondet_uint();
            assume (stateIdx < MAX_TURN_OBSERVATIONS);
            assume (possiblePostStates.isUsed[stateIdx]);
            reachableStates[next] = possiblePostStates.states[stateIdx];
            if (!FINITE_RUNTIME) { // Restart-free Las-Vegas.
                if (isFinalState(reachableStates[next])) {
                    assume (next == L);
                    result = 1;
                }
            } else {
                unsigned int isFinalTurn = 1;
                for (unsigned int j = 0; j < MAX_TURN_OBSERVATIONS; j++) {
                    if (    possiblePostStates.isUsed[j]
                        && !isFinalState(possiblePostStates.states[j])) {
                        isFinalTurn = 0;
                    }
                }
                if (isFinalTurn) {
                    assume (next == L);
                    result = 1;
                }
            }
        } else if (action == SHUFFLE) {
            /**
             * Apply a nondet shuffle and store the result in
             * the reachableStates array.
             */
            reachableStates[next] = applyShuffle(reachableStates[i]);
            if (isFinalState(reachableStates[next])) {
                assume (next == L);
                result = 1;
            }
        } else {
            // No valid action was chosen. This must not happen.
            assume (next == L);
        }
    }
    return result;
}

/**
 * Determine if a sequence in the start state belongs to the input possibility (0 0).
 */
unsigned int isZeroZero(unsigned int arr[N]) {
    return isZero(arr[0], arr[1]) && isZero(arr[2], arr[3]);
}

/**
 * Determine if a sequence in the start state belongs to the input possibility (0 1).
 */
unsigned int isZeroOne(unsigned int arr[N]) {
    return isZero(arr[0], arr[1]) && isOne(arr[2], arr[3]);
}

/**
 * Determine if a sequence in the start state belongs to the input possibility (1 0).
 */
unsigned int isOneZero(unsigned int arr[N]) {
    return isOne(arr[0], arr[1]) && isZero(arr[2], arr[3]);
}

/**
 * Determine if a sequence in the start state belongs to the input possibility (1 1).
 */
unsigned int isOneOne(unsigned int arr[N]) {
    return isOne(arr[0], arr[1]) && isOne(arr[2], arr[3]);
}

/**
 * Returns if the given sequnce is a input sequence in the start state.
 */
unsigned int inputProbability(unsigned int start,
                              unsigned int arr[N]) {
    assume (start < NUMBER_START_SEQS);
    unsigned int res = 0;
    if (start == 0) {
        res = isZeroZero(arr);
    } else if (start == 1) {
        res = isZeroOne(arr);
    } else if (start == 2) {
        res = isOneZero(arr);
    } else if (start == 3) {
        res = isOneOne(arr);
    }
    return res;
}

int main() {
	// Initialise an empty state
    emptyState = getEmptyState();
    struct state startState = emptyState;

    // We generate the start sequences.
    struct narray start[NUMBER_START_SEQS];
    for (unsigned int i = 0; i < NUMBER_START_SEQS; i++) {
        start[i] = getStartSequence();
    }
    assume (isZeroZero(start[0].arr));

    assume (NUMBER_START_SEQS == 4);
    assume (start[0].arr[0] == start[1].arr[0]);
    assume (start[1].arr[0] != start[2].arr[0]);
    assume (start[2].arr[0] == start[3].arr[0]);

    assume (start[0].arr[2] == start[2].arr[2]);
    assume (start[0].arr[2] != start[1].arr[2]);
    assume (start[1].arr[2] == start[3].arr[2]);

    unsigned int arrSeqIdx[NUMBER_START_SEQS];
    for (unsigned int i = 0; i < NUMBER_START_SEQS; i++) {
        arrSeqIdx[i] = getSequenceIndexFromArray(start[i], startState);
    }

    for (unsigned int i = 0; i < NUMBER_START_SEQS; i++) {
        unsigned int idx = arrSeqIdx[i];
        unsigned int inputPoss = 0;
        unsigned int pos = 0;
        if (WEAK_SECURITY != 2) { // We differentiate the output (i.e., NOT output possibilistic)
            // Assign every sequence to their input possibility.
            inputPoss = inputProbability(i, start[i].arr);
            pos = i;
        } else {
            // Assign every sequence to their output result.
            inputPoss = !isOneOne(start[i].arr);
        }
        startState.seq[idx].probs.frac[pos].num = inputPoss;
    }

    unsigned int lastStartSeq = NUMBER_START_SEQS - 1;
    unsigned int arrIdx = arrSeqIdx[lastStartSeq];
    unsigned int lastProbIdx = NUMBER_PROBABILITIES - 1;
    startState.seq[arrIdx].probs.frac[lastProbIdx].num = isOneOne(start[lastStartSeq].arr);

    // Store all possible Permutations
    stateWithAllPermutations = getStateWithAllPermutations();

    // Do actions nondeterministically until a protocol is found.
    unsigned int foundValidProtocol = performActions(startState);
    assume (foundValidProtocol);

	// Fail the check iff a protocol is found, so we can read out the trace including the protocol.
    assert (0);
    return 0;
}
