nbtasks=10
id r C T D 
1 6 1 5 5 
2 2 3 30 30 
3 8 3 30 30 
4 9 3 30 30 
5 8 60 720 720 
6 3 12 180 180 
7 7 29 180 180 
8 1 13 180 180 
9 2 4 180 180 
10 4 52 720 720 
id:list_pred |list_succ
1:_ |4 
2:_ |3 
3:2 |5 6 
4:1 |6 7 
5:3 |8 9 
6:3 4 |9 
7:4 |8 9 
8:7 5 |10 
9:6 7 5 |10 
10:9 8 |_ 