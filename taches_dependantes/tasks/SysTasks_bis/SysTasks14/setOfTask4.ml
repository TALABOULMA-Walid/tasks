nbtasks=10
id r C T D 
1 5 1 10 10 
2 6 5 30 30 
3 6 129 900 900 
4 7 1 10 10 
5 1 76 900 900 
6 8 21 180 180 
7 1 1 60 60 
8 6 2 30 30 
9 3 1 30 30 
10 3 50 900 900 
id:list_pred |list_succ
1:_ |3 4 
2:_ |3 4 5 
3:1 2 |7 
4:2 1 |7 
5:2 |6 7 
6:5 |8 
7:4 5 3 |9 
8:6 |10 
9:7 |10 
10:8 9 |_ 
