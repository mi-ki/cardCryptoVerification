#!/bin/bash

# Copyright (C) 2020 Michael Kirsten, Michael Schrempp, Alexander Koch

#    This program is free software; you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation; either version 3 of the License, or
#    (at your option) any later version.

#    This program is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.

#    You should have received a copy of the GNU General Public License
#    along with this program; if not, <http://www.gnu.org/licenses/>.


export LC_NUMERIC=C
export LC_ALL=C

print_help () {
    USAGE=(
    './runTwoCard.sh [--help],show this help'
    './runTwoCard.sh [OPTIONS],run script with options'

    'Mandatory options'
    '-n <value>,number of cards'
    '-l <value>,protocol length'
    'Possible configurations'
    '--input_poss_security,input-possibilistic security (default: probabilistic security)'
    '--output_poss_security,output-possibilistic security (default: probabilistic security)'
    '--closed,limit search to closed protocols, i.e. only closed shuffles'
    '--max_perm_set_size,<value>,set maximal permutazion set size'
    '--force_random_cuts,limit the search to random cuts (default: no restriction)'
    '--finite_runtime,finite runtime (default: restart-free Las Vegas)'
    'Output options'
    '--raw,raw output, trace is not parsed'
    '--verbose,output trace in JSON format (terminal output is ommitted), trace is parsed'
    'Any other option is directly passed to cbmc'
    )

    printf "\nUsage:\n\n";
    for i in "${USAGE[@]}"; do
        if  [[ $i = *,* ]]; then
            printf '  %-30s %s\n' "${i%%,*}" "${i#*,}"
        else 
            printf "\n%s\n" "$i"
        fi
    done;
}

print_comments() {
    if [[ "$RAW" -eq 0 ]]; then
        cat
    else
        tee -a "$OUTFILE"
    fi
}

declare -A title_map=(
    [WEAK_SECURITY=0]="probabilistic security"
    [WEAK_SECURITY=1]="input-possibilistic security"
    [WEAK_SECURITY=2]="output-possibilistic security"
    [CLOSED=1]="closed protocol"
    [FORCE_RANDOM_CUTS=1]="force random cuts"
    [FINITE_RUNTIME=1]="finite runtime"
    )

VERBOSE=0
CLOSED=0
FINITE_RUNTIME=0
WEAK_SECURITY=-1
FORCE_RANDOM_CUTS=0
RAW=0
MAX_PERM_SET_SIZE=""
N=""
LENGTH=""
UI_OPTS=''
EXTRA_ARGS=()
OPTS_ARRAY=()
#TODO: think about variables for parameters (still needed?)

START=$(date +'%Y-%m-%d %H:%M:%S %Z')
START_PRINT=`echo -e "$START" | sed -e 's/\s/\_/g' | sed -e 's/\-/\_/g' | sed -e 's/:/\_/g'`
START_SEC=$(date +%s)
TIMESTAMP="# Timestamp: "$START
CBMC='./cbmc'
TIMEOUT="5d"

# Input parameters
if [[ $# -eq 0 ]]; then
    echo "No valid options specified. Now terminating"
    exit 1;
fi

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)    
      print_help;
      exit 0 ;;
    -n)
      [[ $# -ge 2 && $2 != -* && ( $# -eq 2 || $3 == -* ) ]] || {
        printf 'No valid card number specified. Now terminating\n'
        exit 2
      }
      N=$2; shift 2 ;;
    -l)
      [[ $# -ge 2 && $2 != -* && ( $# -eq 2 || $3 == -* ) ]] || {
        printf 'No valid protocol length specified. Now terminating.\n'
        exit 2
      }
      LENGTH=$2; shift 2 ;;
    -v|--verbose) VERBOSE=1; shift ;;
    -r|--raw) RAW=1; shift ;;
    --closed) CLOSED=1; OPTS_ARRAY+=("CLOSED_PROTOCOL,$CLOSED"); shift ;;
    --force_random_cuts) FORCE_RANDOM_CUTS=1; OPTS_ARRAY+=("FORCE_RANDOM_CUTS,$FORCE_RANDOM_CUTS"); shift ;;
    --max_perm_set_size)
      [[ $# -ge 2 && $2 != -* && ( $# -eq 2 || $3 == -* ) ]] || {
        printf 'Invalid number of arguments for %s. Now terminating.\n' "$1"
        exit 2
      }
      MAX_PERM_SET_SIZE=$2; OPTS_ARRAY+=("MAX_PERM_SET_SIZE,$2"); shift 2 ;;
    --input_poss_security) 
      (($WEAK_SECURITY == -1)) || {
         printf 'Ambiguous security level. Now terminating.\n'
         exit 2
      }
      WEAK_SECURITY=1;
      OPTS_ARRAY+=("WEAK_SECURITY,$WEAK_SECURITY");
      shift ;;
    --output_poss_security) 
      (($WEAK_SECURITY == -1)) || {
         printf 'Ambiguous security level. Now terminating.\n'
         exit 2
      }
      WEAK_SECURITY=2; 
      OPTS_ARRAY+=("WEAK_SECURITY,$WEAK_SECURITY");
      shift ;;
    --prob_security) 
      (($WEAK_SECURITY == -1)) || {
         printf 'Ambiguous security level. Now terminating.\n'
         exit 2
      }
      WEAK_SECURITY=0; 
      OPTS_ARRAY+=("WEAK_SECURITY,$WEAK_SECURITY");
      shift ;;
    --finite_runtime) FINITE_RUNTIME=1; OPTS_ARRAY+=("FINITE_RUNTIME,$FINITE_RUNTIME") ;shift ;;
    --) shift; break ;;
    -*|--*)
      EXTRA_ARG="$1"
      shift
      while [[ $# -gt 0 && $1 != -* ]]; do
        EXTRA_ARG+=" $1"
        shift
      done
      EXTRA_ARGS+=("$EXTRA_ARG")
      ;;
    *) break ;;
  esac
done

if (( "$RAW" == 0 )); then
    UI_OPTS='--json-ui'
fi


OPTS=''                            # Options passed to cbmc
PRINT_OPTS=''                      # Options that are printed
TITLE_OPTS="N = $N, L = $LENGTH"   # Options in the plot title

if (( ${#OPTS_ARRAY[@]} != 0 )); then
    for i in "${OPTS_ARRAY[@]}"; do
        prettyOpt="${i%%,*} = ${i#*,}"
        shortOpt="${i%%,*}=${i#*,}"

        if [ "$PRINT_OPTS" != "" ]; then
            PRINT_OPTS+=", "
        fi
        OPTS+="-D ${shortOpt} "
        PRINT_OPTS+="${i%%,*} = ${i#*,}"

        # TODO comment?
        if [[ -v title_map[$shortOpt] ]]; then
            TITLE_OPTS+=", ${title_map[$shortOpt]}"
        else
            prettyOpt=$(echo $prettyOpt | tr '[:upper:]' '[:lower:]'  | tr '_' ' ')
            TITLE_OPTS+=", ${prettyOpt}" 
        fi
    done
    PRINT_OPTS="\n# Further Options: $PRINT_OPTS"
fi

echo "titleOPts: $TITLE_OPTS"


#TODO move somewhere else?
if [[ "$WEAK_SECURITY" == -1 ]]; then
    WEAK_SECURITY=0
    OPTS+="-D WEAK_SECURITY=$WEAK_SECURITY"
    echo -e "Security level not set. Using probabilistic security."
fi

# Filter extra arguments for exact duplicates
if [ ${#EXTRA_ARGS[@]} -ne 0  ]; then
    printf "Any additional argument may lead to unexpected behaviour!\n"
    FILTERED_EXTRA_ARGS=()
    readarray -td '' FILTERED_EXTRA_ARGS < <(printf '%s\0' "${EXTRA_ARGS[@]}" | sort -uz)
    JOINED_EXTRAS="$(printf "%s" "${FILTERED_EXTRA_ARGS[*]}")" # Join the array into a single string
fi


NUM_SYM='2' # This is the setting where all cards carry only two distinct symbols
if [ ! -d /Protocols ]; then
  mkdir -p Protocols;
fi

FILE="findTwoCardProtocol.c"
HOST=`echo -e $(hostname)`
FILENAME="Protocols/twoCardProtocol_"$HOST"_"$START_PRINT""
OUTFILE="$FILENAME.out"
TRACE_OPTS='--compact-trace --trace-hex'
INSTR_OPTS='--no-standard-checks'
CBMC_VERBOSITY='--verbosity 9'


if [[ $N == "" ]] || (( "$N" <= "0" ))
then
    echo -e "No valid card number specified. Now terminating."
    exit
fi

FOUR='4' # To be changed when we support more card numbers
if [ "$N" -lt $FOUR ]
then
    echo -e "Program only supports a minimum of "$FOUR" cards, you entered "$N". Now terminating."
    exit
fi

EIGHT='8' # To be changed when we support more card numbers
if [ "$N" -gt $EIGHT ]
then
    echo -e "Program only supports a maximum of "$EIGHT" cards, as we do not know the number of subgroups for greater numbers. You entered the value "$N". Now terminating."
    exit
fi

TWO='2' # Decks with only one distinguishable card are kind of senseless
if [ "$NUM_SYM" -lt $TWO ]
then
    echo -e "Program only supports a minimum number of two distinct card symbols. You entered the value "$NUM_SYM" for distinct symbols. Now terminating."
    exit
fi

# Decks with more distinguishable cards than total cards can probably be represented in some other way using less distinguishable cards.
if [ "$NUM_SYM" -gt $N ]
then
    echo -e "Program only supports a number of possible distinct cards which equals at most the total number of cards. You entered the value "$NUM_SYM" for distinct symbols, where there are only "$N" cards in total. Now terminating."
    exit
fi

if [[ $LENGTH == "" ]] || (( "$LENGTH" <= "0" ))
then
    echo -e "No valid protocol length specified. Now terminating."
    exit
fi

if [ ! -f $FILE ]
then
    echo -e $FILE" is not a valid file. Now terminating."
    exit
fi


CBMC_BINARY=${CBMC#"./"}
if ! [ -x "$(command -v $CBMC_BINARY)" ] && [ ! -f $CBMC ]
then
    echo -e $CBMC_BINARY" is not a valid cbmc binary. Now terminating."
    exit
fi
if [ ! -f $CBMC ]
then
    CBMC=$CBMC_BINARY
fi
VERSION="# CBMC Version: "$($CBMC -version)


fact ()
{
  local number=$1
  #  Variable "number" must be declared as local,
  #+ otherwise this doesn't work.
  if [ "$number" -eq 0 ]
  then
    factorial=1    # Factorial of 0 = 1.
  else
    let "decrnum = number - 1"
    fact $decrnum  # Recursive function call (the function calls itself).
    let "factorial = $number * $?"
  fi

  return $factorial
}


NOM='0'
DENOM='1'
VAL=$[$N / $NUM_SYM]
fact $VAL
FACT=$factorial
BOUND=$[$NUM_SYM - 1]

for i in $(eval echo "{1..$BOUND}")
do
    NOM=$[$NOM + $VAL]
    DENOM=$[$DENOM * $FACT]
done

REST=$[$N - $NOM]
fact $REST
FACT=$factorial
DENOM=$[$DENOM * $FACT]

fact $N
FACT=$factorial

POS_SEQ=$[$FACT / $DENOM]
POS_SEQ_STRING="NUMBER_POSSIBLE_SEQUENCES"

POS_PERM=$FACT
POS_PERM_STRING="NUMBER_POSSIBLE_PERMUTATIONS"

NUMBER_CLOSED_SHUFFLES=(0 1 2 6 30 156 1455 11300 151221)
PERM_SET_SIZE="${NUMBER_CLOSED_SHUFFLES[$N]}"

FIVE='5' # To be changed when we support more card numbers
THREE='3'
SUBGROUP_SIZES=""

# if we had something like this:
# Hard-coded values, look up at https://groupprops.subwiki.org/wiki/Subgroup_structure_of_symmetric_group:S5
# * (We could even omit the largest number here, even)
# * S5_subgroup_sizes = {1, 2, 3, 4, 5, 6, 8, 10, 12, 20, 24, 60, 120} // leave out 1, 120
# * S4_subgroup_sizes = {1, 2, 3, 4, 6, 8, 12, 24} // leave out 1, 24
# * S3_subgroup_sizes = {1, 2, 3, 6} // leave out 1, 6
# * we could check for permSetSize being equal to one of the numbers in the list
if [ "$N" -gt $FIVE ]
then
    NUMBER_SUBGROUP_SIZES='0'
elif [ "$N" -eq $FIVE ]
then
    NUMBER_SUBGROUP_SIZES='11' # We can leave out 1 and 120
    SUBGROUP_SIZES=$SUBGROUP_SIZES" -D SUBGROUP_SIZE_1=2 -D SUBGROUP_SIZE_2=3 -D SUBGROUP_SIZE_3=4 -D SUBGROUP_SIZE_4=5"
    SUBGROUP_SIZES=$SUBGROUP_SIZES" -D SUBGROUP_SIZE_5=6 -D SUBGROUP_SIZE_6=8 -D SUBGROUP_SIZE_7=10 -D SUBGROUP_SIZE_8=12"
    SUBGROUP_SIZES=$SUBGROUP_SIZES" -D SUBGROUP_SIZE_9=20 -D SUBGROUP_SIZE_10=24 -D SUBGROUP_SIZE_11=60 "
elif [ "$N" -eq $FOUR ]
then
    NUMBER_SUBGROUP_SIZES='6' # We can leave out 1 and 24
    SUBGROUP_SIZES=$SUBGROUP_SIZES" -D SUBGROUP_SIZE_1=2 -D SUBGROUP_SIZE_2=3 -D SUBGROUP_SIZE_3=4 "
    SUBGROUP_SIZES=$SUBGROUP_SIZES" -D SUBGROUP_SIZE_4=6 -D SUBGROUP_SIZE_5=8 -D SUBGROUP_SIZE_6=12 "
elif [ "$N" -eq $THREE ]
then
    NUMBER_SUBGROUP_SIZES='2' # We can leave out 1 and 6
    SUBGROUP_SIZES=$SUBGROUP_SIZES" -D SUBGROUP_SIZE_1=2 -D SUBGROUP_SIZE_2=3 "
else
    NUMBER_SUBGROUP_SIZES='0'
fi


COMMAND="$CBMC $JOINED_EXTRAS $UI_OPTS $INSTR_OPTS $TRACE_OPTS -D L=$LENGTH -D N=$N -D NUM_SYM=$NUM_SYM -D $POS_SEQ_STRING=$POS_SEQ -D $POS_PERM_STRING=$POS_PERM -D PERM_SET_SIZE=$PERM_SET_SIZE -D NUMBER_SUBGROUP_SIZES=$NUMBER_SUBGROUP_SIZES $SUBGROUP_SIZES $FILE $OPTS $CBMC_VERBOSITY"

{
    printf '\n%s\n' '############################################################'
    printf '%s\n%s\n' "$TIMESTAMP" "$VERSION"
    printf '%b\n' "# Options: N = $N, NUM_SYM = $NUM_SYM, L = $LENGTH, NUMBER_POSSIBLE_PERMUTATIONS = $POS_PERM, NUMBER_POSSIBLE_SEQUENCES = $POS_SEQ, TIMEOUT = $TIMEOUT$PRINT_OPTS"
    if [[ "$VERBOSE" -eq 1 ]]; then
        printf '%s\n' "# Command: $COMMAND"
    fi
    printf '%s\n' '############################################################'
    printf '\n%s\n\n' '############################################################'
} 2>&1 | print_comments


CBMC_JSON=""$FILENAME"_tmp.out"
if [[ "$RAW" -eq 0 ]]; then
    # output geht nirgendwo hin?
    ##{ time $COMMAND 2>&1 | tee -a $OUTFILE >/dev/null ; } 2> out.time & 
    #{ time $COMMAND 2>&1 | tee -a $OUTFILE ; } 2> time.log &
    timeout $TIMEOUT $COMMAND 2>&1 | tee -a $CBMC_JSON >/dev/null & 
    TIMEOUT_PID=`jobs -p`
    #echo "Timout pid: $TIMEOUT_PID"
else 
    timeout $TIMEOUT $COMMAND 2>&1 | tee -a $OUTFILE  & 
    TIMEOUT_PID=`jobs -p`
fi
    CBMC_PID=$(ps -o pid= --ppid "$TIMEOUT_PID")
    #echo "CBMC_PID: $CBMC_PID"
    #ps -p $CBMC_PID
    #echo time.log


#timeout "$TIMEOUT" time -q -f 'CBMC runtime: %e seconds' $COMMAND 2>&1 | tee -a "$OUTFILE" &
#TIMEOUT_PID=$(jobs -p)
#
#TIME_PID=$(ps -o pid= --ppid "$TIMEOUT_PID" | awk 'NR == 1 {print $1}')
#CBMC_PID=$(ps -o pid= --ppid "$TIME_PID" | awk 'NR == 1 {print $1}')


# Memory logging 
MEM_VALS=()
PLT_VALS=()
CMD=''
CPU_VAL=0
MEM_VAL=0
SEC=''

if [[ "$VERBOSE" -eq 1 ]]; then
    top -b -n 1 -p "$CBMC_PID" | sed -n '8,12p' | awk '{print $12, $9, $10, $11}'
    while kill -0 "$CBMC_PID" 2>/dev/null; do

        if [ -n "$CBMC_PID" ]; then
            {
                read -r CMD CPU_VAL MEM_VAL SEC < <(
                    top -b -n 1 -p "$CBMC_PID" | sed -n '8,12p' | awk '{print $12, $9, $10, $11}'
                )

                ELAPSED_SECONDS=$(awk -F '[:.]' '{print $1 * 60 + $2}' <<< "$SEC")

                printf "\n[%s] %s - CPU: %s%% - MEM: %s%%\n" "$(date +"%Y-%m-%d %H:%M:%S %Z")" "$CMD" "$CPU_VAL" "$MEM_VAL"
                MEM_VALS+=("$MEM_VAL")
                PLT_VALS+=("$ELAPSED_SECONDS $MEM_VAL")
            } 
        fi
        sleep 5
    done
fi

wait $TIMEOUT_PID


END=$(date +'%Y-%m-%d %H:%M:%S %Z')
END_SEC=$(date +%s)
FINAL_TIMESTAMP="# Final Time: "$END
DIFF=$(( $END_SEC - $START_SEC ))


# 3. schlau anordnen 
if [[ "$RAW" -eq 0 ]]; then
    jq -n \
        --arg startTime "$START" \
        --arg timeout "$TIMEOUT" \
        --argjson numSym "$NUM_SYM" \
        --argjson length "$LENGTH" \
        --argjson weakSecurity "$WEAK_SECURITY" \
        --argjson forceRandomCuts "$FORCE_RANDOM_CUTS" \
        --argjson closed "$CLOSED" \
        --argjson numberPossiblePermutations "$POS_PERM" \
        --argjson numberPossibleSequences "$POS_SEQ" \
        --arg command "$COMMAND" \
        --slurpfile cbmcOutput "$CBMC_JSON" \
        --arg finalTime "$FINAL_TIMESTAMP" \
        --arg runningTime "$DIFF" \
        '$ARGS.named + {cbmcOutput: $cbmcOutput[0]}' > $OUTFILE

    #TODO: what to do when SIGINT?
    rm "$CBMC_JSON" 
fi



{
    printf '\n%s\n' '#####################################################################'
    printf '%s\n' "$FINAL_TIMESTAMP"
    printf '%s\n' "# It took $DIFF seconds."
    printf '%s\n' '#####################################################################'
} 2>&1 | print_comments

# Parse statistics from output file
stats=()
runtimes=()

# Read statistics (runtimes, number of variables and clauses, solver) from the outfile
parse_stats() {
    awk '
        /variables/ && /clauses/ {
            c = split($0, b, ",")
            for (i = 1; i <= c; i++) {
                l = split(b[i], v)
                printf "%s: %i\n", v[2], v[1]
            }
            next
        }
        /Runtime\s/ { print }
        /Solving with/ {
            line = $0
            sub(/^.*Solving with[[:space:]]*/, "", line)
            printf "Solver: %s\n", line
        }    '
}

while IFS= read -r line; do
    if [[ $line == 'R'* ]]; then 
        runtimes+=("$line")
    else
        stats+=("$line")
    fi    
done < <(
    # In case of a raw output, read directly from the outfile
    if [[ "$RAW" -eq 1 ]]; then
        parse_stats < "$OUTFILE"
    # If the outfile is in JSON-Format, filter the values of "messageText" first
    else
        jq -r '.cbmcOutput[] | select(.messageText != null) | .messageText' "$OUTFILE" | parse_stats
    fi
)

# Print statistics
for i in "${stats[@]}"; do
    printf '|  %-30s | %-32s|\n' "${i%%:*}" "${i#*:}"
done
printf '%s\n' '----------------------------------+----------------------------------'
for i in "${runtimes[@]}"; do
    printf '|  %-30s | %-32s|\n' "${i%%:*}" "${i#*:}"
done
printf '%s\n' '#####################################################################'


if [[ "$VERBOSE" -eq 1 ]]; then

    if (( ${#PLT_VALS[@]} > 0 && ${#MEM_VALS[@]} > 0)); then

        # Compute statistics
        MIN_MEM=999999
        MAX_MEM=0
        AVG_MEM=0
        MEM_SUM=0

        for VAL in "${MEM_VALS[@]}" 
        do
            MEM_SUM=$(awk -v val=$VAL -v sum=$MEM_SUM 'BEGIN { printf "%.6f", sum + val }')

            if (( $(echo $VAL $MAX_MEM | awk '{if ($1 > $2) print 1;}') )); then
                MAX_MEM="$VAL"
            fi
            if (( $(echo $VAL $MIN_MEM | awk '{if ($1 < $2) print 1;}') )); then
                MIN_MEM="$VAL"
            fi
        done

        VALS_COUNT="${#MEM_VALS[@]}"
        if [ $VALS_COUNT -eq 0 ]; then
            #TODO
            echo "ERROR" 
        else
            AVG_MEM=$(awk -v count=$VALS_COUNT -v sum=$MEM_SUM 'BEGIN { printf "%.2f", sum / count }')
        fi


        # Generate plot
        {
            printf "set terminal svg\n"
            printf "set output '%s_plot.svg'\n" "$FILENAME"
            printf "set tics\n"
            printf "set xlabel 'Time (Seconds)'\n"
            printf "set ylabel 'Memory usage (%%)'\n"
            printf 'set title "%s\\n%s" noenhanced\n' "$FILENAME" "$TITLE_OPTS"
            #printf "plot '-' using 1:2:xtic(1) with lines title 'Memory'\n"
            printf "plot '-' using 1:2 with linespoints notitle\n"
            printf '%s\n' "${PLT_VALS[@]}"
            printf "e\n"
        } | gnuplot

        # Write statiscs to file
        printf "Min. memory usage: %s\nMax. memory usage: %s\nAvg. memory usage: %s\n\n" "$MIN_MEM" "$MAX_MEM" "$AVG_MEM" > "$FILENAME.dat"

        printf "sec %%mem\n" >> "$FILENAME.dat"
        printf "%s\n" "${PLT_VALS[@]}" >> "$FILENAME.dat"

    else
        printf "Data is missing, cannot generate plot.\n\n"
    fi

fi


# Parser
if [[ "$RAW" -eq 0 ]]; then
   #TODO check if trace/outfile exists?
   if [ "$MAX_PERM_SET_SIZE" == "" ]; then
     MAX_PERM_SET_SIZE="$POS_PERM"
   fi
 
    #TODO: use this everywhere or move to top?
    SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
    echo "$SCRIPT_DIR"
 
    cd Parser 2> /dev/null
    if [ $? -ne 0 ]; then
        echo "Parser not found."
        exit 1
    fi
  
    if [[ ! -x ./Parser ]]; then
      echo "Parser not found or not executable. Building parser now."
      make || {
          echo "Build failed. Now terminating." >&2
          exit 1
      }
    fi

    ./Parser ""$SCRIPT_DIR"/"$OUTFILE"" "$LENGTH" "$N" "$NUM_SYM" "$POS_PERM" "$POS_SEQ" "$WEAK_SECURITY" "$MAX_PERM_SET_SIZE"
  
    PARSER_STATUS=$?
    if [ $? -ne 0 ]; then
        echo "Error in parsing."
    fi
fi