nbtasks=10
id r C T D 
1 3 91 900 900 
2 6 38 900 900 
3 4 2 30 30 
4 4 2 30 30 
5 0 3 30 30 
6 0 99 900 900 
7 0 22 180 180 
8 1 39 900 900 
9 8 1 10 10 
10 3 13 180 180 
id:list_pred |list_succ
1:_ |3 4 
2:_ |3 4 
3:2 1 |_ 
4:2 1 |5 6 
5:4 |7 8 9 
6:4 |7 8 
7:5 6 |10 
8:6 5 |10 
9:5 |10 
10:8 7 9 |_ 
