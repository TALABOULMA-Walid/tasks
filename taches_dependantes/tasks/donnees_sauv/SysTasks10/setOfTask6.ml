nbtasks=10
id r C T D 
1 5 111 900 900 
2 2 26 180 180 
3 4 16 180 180 
4 9 15 180 180 
5 1 55 900 900 
6 7 3 30 30 
7 1 3 180 180 
8 5 85 900 900 
9 8 77 900 900 
10 5 1 30 30 
id:list_pred |list_succ
1:_ |3 
2:_ |4 
3:1 |5 6 
4:2 |5 6 7 
5:3 4 |8 9 
6:4 3 |8 9 
7:4 |8 9 
8:7 6 5 |10 
9:5 7 6 |10 
10:8 9 |_ 
