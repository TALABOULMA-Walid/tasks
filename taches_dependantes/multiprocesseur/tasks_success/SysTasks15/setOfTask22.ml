nbtasks=10
id r C T D 
1 662 67 730 730 
2 5277 1448 8760 8760 
3 3806 795 4380 4380 
4 8173 102 730 730 
5 9776 1024 8760 8760 
6 8173 64 1460 1460 
7 11824 1 10 10 
8 11221 247 4380 4380 
9 12546 38 730 730 
10 20576 581 8760 8760 
id:list_pred |list_succ
1:_ |4 5 
2:_ |4 5 6 
3:_ |4 5 6 
4:1 2 3 |_ 
5:3 2 1 |7 
6:3 2 |8 
7:5 |9 10 
8:6 |9 10 
9:7 8 |_ 
10:8 7 |_ 
