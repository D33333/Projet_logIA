#!/usr/bin/env bash

CALL_PATH="$(dirname "$0")"

RESULT_PASS=0
FILE_PASS=$(mktemp)
RESULT_WRONG=0
FILE_WRONG=$(mktemp)
RESULT_TIMEOUT=0
FILE_TIMEOUT=$(mktemp)
RESULT_FAIL=0
FILE_FAIL=$(mktemp)
TOTAL=0

TIMEOUT=${1:-30}
CMD="timeout ${TIMEOUT} ./cdcl --proof"
CMD_PROOF="picosat"

JOBS=${2:-4}

function displayWrong()   { tput setaf 1; echo "WRONG";   RESULT_WRONG=$(( RESULT_WRONG + 1 ));    tput setaf 7; }
function displayWrongResult() { tput setaf 1; echo "WRONG_RES"; RESULT_WRONG=$(( RESULT_WRONG + 1)); tput setaf 7; }
function displaySuccess() { tput setaf 2; echo "SUCCESS"; RESULT_PASS=$(( RESULT_PASS + 1 ));      tput setaf 7; }
function displayTimeout() { tput setaf 3; echo "TIMEOUT"; RESULT_TIMEOUT=$(( RESULT_TIMEOUT + 1)); tput setaf 7; }
function displayFail()    { tput setaf 4; echo "FAIL";    RESULT_FAIL=$(( RESULT_FAIL + 1 ));      tput setaf 7; }

# void launchSatisfiableTest(String filePath)
function launchSatisfiableTest()
{
    local FILEPATH="$1"
    SANITY=$(${CMD_PROOF} "${FILEPATH}")
    RESULT=$(${CMD} "${FILEPATH}")
    ECODE=$?

    echo -n "${FILEPATH}... "

    if [[ ${SANITY:2} = SATISFIABLE* ]]; then
        echo "Sanity check passed"
    else
        tput setaf 1; echo "Sanity check failed!"; tput setaf 7
    fi


    if [[ $ECODE -eq 124 ]]; then
        echo $FILEPATH >> $FILE_TIMEOUT
        displayTimeout
    else
        if [[ ${RESULT} = true* ]]; then
            local PROOF=$(echo " ${RESULT:6}" | tr '\n' ' ' | sed 's/ / -a /g')
            local CHECK=$(${CMD_PROOF} "${FILEPATH}" ${PROOF:1:-4})

            if [[ ${CHECK:2} = SATISFIABLE* ]]; then
                echo $FILEPATH >> $FILE_PASS
                displaySuccess
            else
                echo $FILEPATH >> $FILE_WRONG
                displayWrong
            fi

        elif [[ ${RESULT} = false ]]; then
            echo $FILEPATH >> $FILE_WRONG
            displayWrongResult
        else
            echo $FILEPATH >> $FILE_FAIL
            displayFail
        fi
    fi
}
export -f launchSatisfiableTest

# void launchUnsatisfiableTest(String filePath)
function launchUnsatisfiableTest()
{
    local FILEPATH="$1"
    SANITY=$(${CMD_PROOF} "${FILEPATH}")
    RESULT=$(${CMD} "${FILEPATH}")
    ECODE=$?

    echo -n "${FILEPATH}... "

    if [[ ${SANITY:2} = SATISFIABLE* ]]; then
        tput setaf 1; echo "Sanity check failed!"; tput setaf 7
    else
        echo "Sanity check passed"
    fi

    if [[ $ECODE -eq 124 ]]; then
        echo $FILEPATH >> $FILE_TIMEOUT
        displayTimeout
    else
        if [[ ${RESULT} = true* ]]; then
            echo $FILEPATH >> $FILE_WRONG
            displayWrongResult
        elif [[ ${RESULT} = false ]]; then
            echo $FILEPATH >> $FILE_PASS
            displaySuccess
        else
            echo $FILEPATH >> $FILE_FAIL
            displayFail
        fi
    fi
}
export -f launchUnsatisfiableTest

. env_parallel.bash

echo ""
echo "------------------------"
echo "  Running satisfiable tests with TIMEOUT=$TIMEOUT"
echo "------------------------"

#while IFS= read -r -d '' FILE; do
#
    #launchSatisfiableTest "${FILE}"
#
    #TOTAL=$(( TOTAL + 1 ))
#
#done < <(find "${CALL_PATH}/OK" -name "*.cnf" -print0)
env_parallel --use-cpus-instead-of-cores -j $JOBS launchSatisfiableTest < <(find "${CALL_PATH}/OK" -name "*.cnf" -print)


echo ""
echo "------------------------"
echo "  Running unsatisfiable tests with TIMEOUT=$TIMEOUT"
echo "------------------------"

#while IFS= read -r -d '' FILE; do
#
    #launchUnsatisfiableTest "${FILE}"
#
    #TOTAL=$(( TOTAL + 1 ))
#
#done < <(find "${CALL_PATH}/KO" -name "*.cnf" -print0)
env_parallel --use-cpus-instead-of-cores -j $JOBS launchUnsatisfiableTest < <(find "${CALL_PATH}/KO" -name "*.cnf" -print)

RESULT_WRONG=$(wc -l < $FILE_WRONG)
RESULT_PASS=$(wc -l < $FILE_PASS)
RESULT_TIMEOUT=$(wc -l < $FILE_TIMEOUT)
RESULT_FAIL=$(wc -l < $FILE_FAIL)
TOTAL=$(( RESULT_PASS + RESULT_WRONG + RESULT_FAIL + RESULT_TIMEOUT ))

rm $FILE_FAIL
rm $FILE_TIMEOUT
rm $FILE_PASS
rm $FILE_WRONG

tput setaf 1; echo "Wrong  : ${RESULT_WRONG} / ${TOTAL}"; tput setaf 7
tput setaf 2; echo "Pass   : ${RESULT_PASS} / ${TOTAL}"; tput setaf 7
tput setaf 3; echo "Timeout: ${RESULT_TIMEOUT} / ${TOTAL}"; tput setaf 7
tput setaf 4; echo "Fail   : ${RESULT_FAIL} / ${TOTAL}"; tput setaf 7
