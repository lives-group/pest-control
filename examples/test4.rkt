#lang pest-control/debug/untyped

forever1 <-- (push(epsilon) ~ pop)[0,infty];
forever2 <-- peekall ~ (peekall)[0,infty];
forever3 <-- forever3;
start: forever1