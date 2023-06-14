#!/bin/bash
PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games
#s SATISFIABLE
#v 1 0

LING=$PWD/lingeling
FORMULA=$1
ARQ=$3
OK=$4

ulimit -t 5000

RESP=
if [[ "$PRINTCNF" == "1" ]]; then
#  date >> /tmp/printcnf
 RESP="$(./fortalecedor < $FORMULA | $LING $FORMULA| egrep '^(v|s)')"
else
 RESP="$($LING $FORMULA| egrep '^(v|s)')"
fi

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

(echo SATISFIABLE; grep '^v' <<< "$RESP" | tr -d 'v' | sed -e 's/ 0$//' | tr -d '\n'
echo) > $ARQ
if [[ "x$OK" != "x" ]]; then
 echo feito > $OK
fi
exit 0