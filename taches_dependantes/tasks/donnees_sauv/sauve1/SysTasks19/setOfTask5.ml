nbtasks=10
id r C T D 
1 3 4 30 30 
2 0 39 360 360 
3 4 1 10 10 
4 3 27 360 360 
5 4 33 180 180 
6 8 3 30 30 
7 2 56 720 720 
8 3 4 30 30 
9 7 60 720 720 
10 8 1 30 30 
id:list_pred |list_succ
1:_ |3 4 
2:_ |_ 
3:1 |5 6 
4:1 |5 
5:3 4 |7 8 9 
6:3 |7 8 9 
7:6 5 |10 
8:5 6 |10 
9:6 5 |10 
10:9 8 7 |_ 