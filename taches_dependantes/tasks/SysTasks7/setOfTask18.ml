nbtasks=10
id r C T D 
1 3 1 30 30 
2 7 1 30 30 
3 0 3 30 30 
4 7 3 30 30 
5 0 1 10 10 
6 4 1 10 10 
7 5 2 30 30 
8 4 89 900 900 
9 1 8 180 180 
10 1 4 180 180 
id:list_pred |list_succ
1:_ |3 
2:_ |4 
3:1 |5 6 
4:2 |5 6 7 
5:4 3 |9 
6:3 4 |8 
7:4 |9 
8:6 |10 
9:7 5 |10 
10:8 9 |_ 