nbtasks=10
id r C T D 
1 6 1 60 60 
2 9 6 180 180 
3 4 1 10 10 
4 4 76 900 900 
5 6 17 180 180 
6 7 11 180 180 
7 8 49 900 900 
8 9 1 60 60 
9 0 2 180 180 
10 4 8 180 180 
id:list_pred |list_succ
1:_ |3 4 
2:_ |3 4 
3:2 1 |_ 
4:2 1 |5 6 7 
5:4 |8 9 
6:4 |8 9 
7:4 |8 
8:7 6 5 |10 
9:6 5 |10 
10:8 9 |_ 
