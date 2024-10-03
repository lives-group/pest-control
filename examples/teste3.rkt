#lang pest-control/debug/untyped

bit <-- '0' / '1';
byte <-- bit^8;
fistFour <-- '1'~'3'~'7' ~ '8'~'0' ~ '7'~'8' ~ '7'~'1';
sndFour <-- '1'~'3' ~ '1'~'0' ~ '2'~'6' ~ '1'~'0';
signature <-- firstFour ~ sndFour;
length <-- push(byte^4);
type <-- byte^4;
data <-- byte^top.tonat;
crc <-- byte^4;
start: signature ~ length ~ type ~ data ~ crc