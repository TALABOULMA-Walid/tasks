nbtasks=10
id r C T D 
1 4 4 30 30 
2 3 13 180 180 
3 8 21 180 180 
4 2 18 180 180 
5 1 46 900 900 
6 6 10 180 180 
7 7 36 900 900 
8 4 3 30 30 
9 0 61 900 900 
10 1 5 180 180 
id:list_pred |list_succ
1:_ |3 4 
2:_ |4 
3:1 |5 6 
4:1 2 |6 
5:3 |7 8 9 
6:4 3 |7 9 
7:6 5 |10 
8:5 |10 
9:6 5 |10 
10:8 7 9 |_ 
