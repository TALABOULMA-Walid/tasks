nbtasks=10
id r C T D 
1 4 112 900 900 
2 3 1 10 10 
3 4 3 30 30 
4 6 1 10 10 
5 1 21 180 180 
6 9 17 180 180 
7 3 23 180 180 
8 4 5 180 180 
9 5 2 60 60 
10 8 62 900 900 
id:list_pred |list_succ
1:_ |4 
2:_ |3 
3:2 |_ 
4:1 |5 6 
5:4 |7 
6:4 |7 8 9 
7:6 5 |10 
8:6 |10 
9:6 |10 
10:9 8 7 |_ 
