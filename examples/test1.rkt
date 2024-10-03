#lang pest-control/debug/untyped

bit <-- '0' ;
byte <-- bit ^ 8;
start: byte ^ 2 ~ bit
