nbtasks=10
id r C T D 
1 315 220 2880 2880 
2 152 190 2880 2880 
3 173 48 720 720 
4 755 12 180 180 
5 5309 492 5760 5760 
6 959 27 360 360 
7 779 19 180 180 
8 1013 4 90 90 
9 6691 396 5760 5760 
10 3811 73 2880 2880 
id:list_pred |list_succ
1:_ |4 
2:_ |5 
3:_ |4 5 
4:1 3 |6 7 
5:3 2 |_ 
6:4 |8 
7:4 |8 
8:6 7 |9 10 
9:8 |_ 
10:8 |_ 