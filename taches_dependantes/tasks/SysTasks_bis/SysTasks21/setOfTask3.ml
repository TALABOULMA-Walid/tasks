nbtasks=10
id r C T D 
1 4 1 10 10 
2 5 100 900 900 
3 2 4 30 30 
4 0 99 900 900 
5 6 18 180 180 
6 5 17 180 180 
7 7 11 180 180 
8 4 23 180 180 
9 4 38 900 900 
10 0 2 30 30 
id:list_pred |list_succ
1:_ |3 4 5 
2:_ |3 4 5 
3:1 2 |6 7 
4:1 2 |_ 
5:1 2 |7 
6:3 |9 
7:5 3 |8 
8:7 |10 
9:6 |10 
10:8 9 |_ 
