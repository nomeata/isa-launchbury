#!/bin/bash

set -e

if [ -z $1 ]
then 
  echo "Usage: $0 foo.tar.gz"
  exit 1
fi

tmpdir=`mktemp -d -t isa-test.XXXXXXXX`

echo "Using temporary directoy $tmpdir"

tar -x -a -v -C $tmpdir -f "$1" 
cd $tmpdir
dir=$(ls -1)
git -C ~/projekte/afp/AFP-git archive Isabelle2014 | tar -x -C .
mv $dir thys/
cd thys/$dir
isabelle build -D .
cd /
echo rm -rf "$tmpdir"
