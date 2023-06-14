#!/bin/bash
PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games
#s SATISFIABLE
#v 1 0

NFLSAT=$PWD/nflsat-iscas
TEMPSOL=$PWD/temp_solution.sol
FORMULA=$1
ARQ=$3
OK=$4

ulimit -t 5000

RESP="$($NFLSAT --iscas --solution $TEMPSOL $FORMULA| egrep '^(v|s)')"

if ! grep -q "s SATISFIABLE" <<< "$RESP" ; then
   if ! grep -q "UNSAT" <<< "$RESP" ; then
       echo "UNKNOWN" > $ARQ
       exit 2
   fi
   echo UNSATISFIABLE > $ARQ
   if [[ "x$OK" != "x" ]]; then
     echo feito > $OK
   fi
   exit 1
fi

printf 's SATISFIABLE\n ' > $ARQ
(cat $TEMPSOL | awk -F= '{ if ($2==1) printf $1" " ; else printf "-"$1" "}' | sed 's/V//g') >> $ARQ
#(cat $TEMPSOL | awk -F= '{printf $2}') >> $ARQ
#(echo SATISFIABLE; grep '^v' <<< "$RESP" | tr -d 'v' | sed -e 's/ 0$//' | tr -d '\n'
#echo) > $ARQ
if [[ "x$OK" != "x" ]]; then
 echo feito > $OK
fi
exit 0
