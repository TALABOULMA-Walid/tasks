nbtasks=10
id r C T D 
1 5 3 30 30 
2 0 2 30 30 
3 3 9 180 180 
4 1 92 900 900 
5 2 3 30 30 
6 4 98 900 900 
7 4 9 180 180 
8 7 57 900 900 
9 2 7 180 180 
10 9 3 30 30 
id:list_pred |list_succ
1:_ |3 5 
2:_ |3 4 
3:1 2 |_ 
4:2 |6 
5:1 |6 7 
6:4 5 |8 9 
7:5 |9 
8:6 |10 
9:6 7 |10 
10:8 9 |_ 