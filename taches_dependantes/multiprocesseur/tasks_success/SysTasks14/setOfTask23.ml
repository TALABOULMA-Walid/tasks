nbtasks=10
id r C T D 
1 3573 541 4080 4080 
2 434 63 680 680 
3 6881 1317 8160 8160 
4 9515 66 680 680 
5 9515 2 20 20 
6 4655 298 4080 4080 
7 10859 95 1360 1360 
8 10859 232 1360 1360 
9 18123 767 8160 8160 
10 11323 12 680 680 
id:list_pred |list_succ
1:_ |4 5 6 
2:_ |4 6 
3:_ |4 5 
4:1 2 3 |7 
5:3 1 |7 8 
6:2 1 |7 
7:6 5 4 |9 10 
8:5 |9 10 
9:8 7 |_ 
10:8 7 |_ 