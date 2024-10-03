#lang pest-control/debug/untyped

number <-- '0' / '1' / '2' / '3' / '4' / '5' / '6' / '7' / '8' / '9';
letter <-- 'a' / 'b' / 'c' / 'd' / 'e'/ 'f' / 'g' / 'h' / 'i' / 'j';
char <-- number / letter;
n <-- number ~ number[0,infty];
start:  push(n) ~ ':' ~ char^top.tonat ~ ','
