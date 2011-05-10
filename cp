#!/bin/bash

runner="./scalac-cp"
newargs=""

for arg in $@
do
    if [ -e ${arg} ]
    then
        newargs="${newargs} ${arg}"
    else
        newargs="${newargs} -P:constraint-programming:${arg}"
    fi
done

if [ -e ${runner} ]
then
    ${runner} ${newargs}
else
    echo "${runner} not found. Have you run 'sbt all' ?"
    exit 1
fi