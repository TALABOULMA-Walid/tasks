nbtasks=10
id r C T D 
1 4 2 30 30 
2 6 3 30 30 
3 2 89 540 540 
4 9 1 10 10 
5 3 5 30 30 
6 2 1 10 10 
7 7 3 180 180 
8 8 15 180 180 
9 3 18 180 180 
10 0 19 540 540 
id:list_pred |list_succ
1:_ |3 
2:_ |4 
3:1 |5 
4:2 |5 6 
5:3 4 |7 8 9 
6:4 |8 9 
7:5 |10 
8:5 6 |10 
9:6 5 |10 
10:7 9 8 |_ 