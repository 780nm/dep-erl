#!/bin/bash

agda --compile dep-red.agda
./dep-red

erlc +debug_info ./reduce.erl
erlc +debug_info ./test.erl
erl -s test