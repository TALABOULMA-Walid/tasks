nbtasks=10
id r C T D 
1 1 3 30 30 
2 1 21 540 540 
3 4 1 10 10 
4 4 2 30 30 
5 2 2 30 30 
6 7 2 30 30 
7 2 13 180 180 
8 1 1 10 10 
9 7 13 180 180 
10 0 1 30 30 
id:list_pred |list_succ
1:_ |4 
2:_ |3 4 
3:2 |5 
4:2 1 |6 
5:3 |7 8 9 
6:4 |7 8 9 
7:5 6 |10 
8:5 6 |10 
9:6 5 |10 
10:7 9 8 |_ 
