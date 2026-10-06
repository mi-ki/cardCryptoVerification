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


START=$(date +'%Y-%m-%d %H:%M:%S %Z')
START_PRINT=`echo -e "$START" | sed -e 's/\s/\_/g' | sed -e 's/\-/\_/g' | sed -e 's/:/\_/g'`
START_SEC=$(date +%s)
TIMESTAMP="# Timestamp: "$START
CBMC='./cbmc'
FILE="findTwoCardProtocol.c"
HOST=`echo -e $(hostname)`
FILENAME="twoCardProtocol_$HOST_$START_PRINT"
OUTFILE="$FILENAME.out"
TRACE_OPTS='--compact-trace --trace-hex'
INSTR_OPTS='--no-standard-checks'
UI_OPTS='--json-ui'
TIMEOUT="5d"
N=$1
LENGTH=$2
OPT=$
NUM_SYM='2' # This is the setting where all cards carry only two distinct symbols

OPTS=''
while [ -n "$3" ]
do
    OPTS=$OPTS" ${3}" && shift;
done
PRINT_OPTS=''
if [ -n "$OPTS" ]
then
    printOpts=`echo -e "?$OPTS" | sed -e 's/?\s--//g' | sed -e 's/?\s-D\s//g' | sed -re 's/([a-zA-Z0-9]+)=([0-9]+)/\1 = \2/g' | sed -e 's/\s-D\s/, /g'`
    printOpts=`echo -e "$printOpts" | sed 's/\s\(.*\)--/\1 and /' | sed 's/--/, /g'`
    PRINT_OPTS=`echo -e "$printOpts" | sed -e 's/and/,/g' | sed 's/[[:space:]]*,/,/g'`
fi
if [ -n "$OPTS" ]
then
    OPTIONS='\n'"# Further Options: "$PRINT_OPTS
else
    OPTIONS=''
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
FOO=$factorial
BOUND=$[$NUM_SYM - 1]

for i in $(eval echo "{1..$BOUND}")
do
    NOM=$[$NOM + $VAL]
    DENOM=$[$DENOM * $FOO]
done

REST=$[$N - $NOM]
fact $REST
FOO=$factorial
DENOM=$[$DENOM * $FOO]

fact $N
FOO=$factorial

POS_SEQ=$[$FOO / $DENOM]
POS_SEQ_STRING="NUMBER_POSSIBLE_SEQUENCES"

POS_PERM=$FOO
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

COMMAND="$CBMC $UI_OPTS $INSTR_OPTS $TRACE_OPTS $INSTR_OPTS -D L=$LENGTH -D N=$N -D NUM_SYM=$NUM_SYM -D $POS_SEQ_STRING=$POS_SEQ -D $POS_PERM_STRING=$POS_PERM -D PERM_SET_SIZE=$PERM_SET_SIZE -D NUMBER_SUBGROUP_SIZES=$NUMBER_SUBGROUP_SIZES $SUBGROUP_SIZES $FILE $OPTS"

echo -e '\n'"############################################################" 2>&1 | tee $OUTFILE
echo -e $TIMESTAMP'\n'$VERSION$OPTIONS 2>&1 | tee -a $OUTFILE
echo -e "# N = "$N", NUM_SYM = "$NUM_SYM", L = "$LENGTH", NUMBER_POSSIBLE_PERMUTATIONS = "$POS_PERM", NUMBER_POSSIBLE_SEQUENCES = "$POS_SEQ", TIMEOUT = "$TIMEOUT 2>&1 | tee -a $OUTFILE
echo -e "# Command: $COMMAND" | tee -a $OUTFILE
echo -e "############################################################" 2>&1 | tee -a $OUTFILE
echo -e '\n'"############################################################"'\n' 2>&1 | tee -a $OUTFILE

timeout $TIMEOUT $COMMAND 2>&1 | tee -a $OUTFILE & 
TIMEOUT_PID=`jobs -p`
CBMC_PID=$(ps -o pid= --ppid "$TIMEOUT_PID")


#timeout "$TIMEOUT" time -q -f 'CBMC runtime: %e seconds' $COMMAND 2>&1 | tee -a "$OUTFILE" &
#TIMEOUT_PID=$(jobs -p)
#
#TIME_PID=$(ps -o pid= --ppid "$TIMEOUT_PID" | awk 'NR == 1 {print $1}')
#CBMC_PID=$(ps -o pid= --ppid "$TIME_PID" | awk 'NR == 1 {print $1}')


# Memory logging 
#CPU_VALS=()  #TODO ggf löschen?
MEM_VALS=()
PLT_VALS=()
COMMAND=''
CPU_VAL=0
MEM_VAL=0
SEC=''

while kill -0 "$CBMC_PID" 2>/dev/null; do
    if [ -n "$CBMC_PID" ]; then
        {  
            read -r COMMAND CPU_VAL MEM_VAL SEC < <(
                top -b -n 1 -p "$CBMC_PID" | sed -n '8,12p' | awk '{print $12, $9, $10, $11}'
            )

            ELAPSED_SECONDS=$(awk -F '[:.]' '{print $1 * 60 + $2}' <<< "$SEC")

            printf "\n[%s] %s - %%CPU: %s  %%MEM: %s\n" "$(date +"%Y-%m-%d %H:%M:%S %Z")" "$COMMAND" "$CPU_VAL" "$MEM_VAL"
            #CPU_VALS+=("$CPU_VAL")
            MEM_VALS+=("$MEM_VAL")
            PLT_VALS+=("$ELAPSED_SECONDS $MEM_VAL")
        } 
    fi
    sleep 5
done


END=$(date +'%Y-%m-%d %H:%M:%S %Z')
END_SEC=$(date +%s)
FINAL_TIMESTAMP="# Final Time: "$END
DIFF=$(( $END_SEC - $START_SEC ))
echo -e '\n'"############################################################" 2>&1 | tee -a $OUTFILE
echo -e $FINAL_TIMESTAMP 2>&1 | tee -a $OUTFILE
echo -e "# It took $DIFF seconds." 2>&1 | tee -a $OUTFILE
echo -e "############################################################" 2>&1 | tee -a $OUTFILE


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
    #printf "plot '-' using 1:2:xtic(1) with lines title 'Memory'\n"
    printf "plot '-' using 1:2 with linespoints title 'Memory'\n"
    printf '%s\n' "${PLT_VALS[@]}"
    printf "e\n"
} | gnuplot


# Write statiscs to file
printf "Min. memory usage: %s\nMax. memory usage: %s\nAvg. memory usage: %s\n\n" "$MIN_MEM" "$MAX_MEM" "$AVG_MEM" > ""$FILENAME"_stats.txt"

printf "sec %%mem\n" >> ""$FILENAME"_stats.txt"
printf "%s\n" "${PLT_VALS[@]}" >> ""$FILENAME"_stats.txt"

