nbtasks=10
id r C T D 
1 4 51 360 360 
2 8 38 720 720 
3 6 1 30 30 
4 1 38 720 720 
5 3 7 180 180 
6 7 1 60 60 
7 5 8 720 720 
8 5 1 10 10 
9 6 46 720 720 
10 6 2 30 30 
id:list_pred |list_succ
1:_ |4 
2:_ |3 
3:2 |5 6 7 
4:1 |5 6 7 
5:4 3 |9 
6:3 4 |8 
7:3 4 |9 
8:6 |10 
9:5 7 |10 
10:9 8 |_ 
