nbtasks=8
id r C T D 
1 2 1 10 10 
2 96 25 210 210 
3 146 46 210 210 
4 146 14 70 70 
5 356 36 420 420 
6 524 64 420 420 
7 652 29 420 420 
8 652 5 70 70 
id:list_pred |list_succ
1:_ |4 
2:_ |3 4 5 
3:2 |6 
4:2 1 |6 
5:2 |6 
6:4 3 5 |7 8 
7:6 |_ 
8:6 |_ 