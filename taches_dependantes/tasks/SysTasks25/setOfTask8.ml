nbtasks=10
id r C T D 
1 21 2 70 70 
2 326 24 350 350 
3 303 8 350 350 
4 350 16 350 350 
5 303 32 350 350 
6 716 30 700 700 
7 335 23 350 350 
8 685 34 700 700 
9 746 60 700 700 
10 746 29 350 350 
id:list_pred |list_succ
1:_ |3 5 
2:_ |4 
3:1 |6 
4:2 |6 
5:1 |6 7 8 
6:3 5 4 |9 10 
7:5 |9 10 
8:5 |9 
9:7 8 6 |_ 
10:6 7 |_ 
