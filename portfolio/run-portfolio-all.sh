DIR=$(dirname $0)

parallel -v "res="'$({}/bin/z3 '$1')'"; if [[ "\"'$res'\"" == "\""unknown"\"" ]]; then exit 1; fi; echo "'$res' ::: $DIR/portfolio/*
