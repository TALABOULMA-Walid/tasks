nbtasks=10
id r C T D 
1 75 190 1550 1550 
2 844 1493 9300 9300 
3 1326 210 1550 1550 
4 3830 29 310 310 
5 3296 205 3100 3100 
6 3830 200 1550 1550 
7 4230 16 310 310 
8 4230 4 310 310 
9 7052 284 3100 3100 
10 5502 125 1550 1550 
id:list_pred |list_succ
1:_ |_ 
2:_ |4 5 6 
3:_ |4 5 
4:2 3 |7 8 
5:3 2 |7 8 
6:2 |7 8 
7:5 6 4 |9 10 
8:6 4 5 |9 10 
9:8 7 |_ 
10:8 7 |_ 