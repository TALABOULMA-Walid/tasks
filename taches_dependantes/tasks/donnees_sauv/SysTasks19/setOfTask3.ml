nbtasks=10
id r C T D 
1 8 2 30 30 
2 8 84 540 540 
3 2 104 540 540 
4 1 27 180 180 
5 3 60 540 540 
6 6 13 540 540 
7 0 1 10 10 
8 8 1 10 10 
9 0 3 30 30 
10 1 23 540 540 
id:list_pred |list_succ
1:_ |3 
2:_ |3 4 
3:1 2 |5 6 7 
4:2 |5 6 7 
5:3 4 |_ 
6:4 3 |8 9 
7:4 3 |8 
8:7 6 |10 
9:6 |10 
10:8 9 |_ 