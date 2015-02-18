#!/bin/bash

set -e

if [ -z $1 ]
then 
  echo "Usage: $0 foo.tar.gz"
  exit 1
fi

dir=`mktemp -d -t isa-test.XXXXXXXX`

echo "Using temporary directoy $dir"

tar -x -a -v -C $dir -f "$1" 
cd $dir/*;
isabelle build -D .
cd /
echo rm -rf "$dir"
