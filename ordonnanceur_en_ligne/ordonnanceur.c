#define _GNU_SOURCE
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <stdio.h>
#include<stdlib.h>
#include<time.h>
#include<unistd.h>
#include<errno.h>
#include<sys/time.h>


int Hyperperiode = 2;
//Struture de données  et variables globales
//Structure de données de T
typedef  struct Element_tab_ordo {
 int id;
 int duree;
 int create_thread; 
 void *(*code)();
// pthread_t * tache; //(*code)();
}ELEMENT_TAB ;

const SIZE_T=6; 
const I_PERM=0; 
const R_MIN=0;

int i=-1;
int i_prec=0;
int j=0;

/*Création des taches(thread)*/
pthread_t Nb_threads[4]; 

/* Code de la tâche 1. tache2=(2,2,6,6) avec une unité de temps est égale à 1s*/ 
void * tache1(){
//int n=sched_getcpu();
printf ("[%f]  Début Task1 sur proc%d\n",(clock()/(double)CLOCKS_PER_SEC),1);
int j=0;  
 while  (j<1000900000){
   j++;
 }
printf ("[%f]  Fin Task1 \n",(clock()/(double)CLOCKS_PER_SEC));
return NULL;
}
/****************************************************************************/
/* Code de la tâche 2. tache2=(0,4,12,12) avec une unité de temps est égale à 1s*/ 
void * tache2(){
//int n=sched_getcpu();
printf ("[%f]  Début Task2 sur proc%d\n",(clock()/(double)CLOCKS_PER_SEC),1);
 int j=0;  
 while  (j< 2000900000){
   j++;
 }
printf ("[%f]  Fin Task2 \n",(clock()/(double)CLOCKS_PER_SEC));
return NULL;
}
/*****************************************************************************/
/* Code de la tâche 3. tache3=(2,2,12,12) avec une unité de temps est égale à 1s*/ 
void * tache3(){
//int n=sched_getcpu();
printf ("[%f]  Début Task3 sur proc%d\n",(clock()/(double)CLOCKS_PER_SEC),1);
 int j=0;   
 while  (j< 1000900000){
   j++;
 }

printf ("[%f]  Fin Task3 \n",(clock()/(double)CLOCKS_PER_SEC));
return NULL;
}
/******************************************************************************/
/* Code de la tâche idle*/ 
void * vide(){
printf ("Début temps libre sur proc%d\n",1);
  int j=0;   
 while  (j< 1000900000){
   j++;
 }
printf ("fin temps libre \n hyperperiode : %d \n", Hyperperiode++);
return NULL;
}
/********************************************************************************/

/******************************************************************************/
/* Code de la tâche idle*/ 
void * idle(){
//printf ("Début idle sur proc%d\n",1);  
 while  (1){
   
 }

return NULL;
}
/********************************************************************************/

// table d'ordonnancement
//ELEMENT_TAB T[]={{2,2,1,tache2},{1,2,1,tache1},{2,3,0,tache2},{3,1,1,tache3},{1,2,1,tache1},{3,2,0,tache3},{2,2,1,tache2}};
ELEMENT_TAB T[]={{2,2,1,tache2},{1,2,1,tache1},{2,2,0,tache2},{3,2,1,tache3},{1,2,1,tache1},{4,2,1,vide}};
// timer logiciel et signal( interruption logicielle)
timer_t timer_o; 
struct sigevent event_o; 
struct itimerspec spec_o; 



/********************************/
/* Fonction ordonnanceur  qui est appelé à chaque expiration du timer timer_o*/
/*Code de l'ordonnanceur*/
void ordonnanceur()
 {
int n=sched_getcpu();
 
 if(i==(SIZE_T-1)){
  i_prec=i;
  i=I_PERM;
  }
 else {
 i_prec=i;
 i++;
}

/*On modifie la durée d'expiration du timer timer_o puis on leré-arme*/
spec_o.it_value.tv_sec=T[i].duree;

if(timer_settime(timer_o,0,&spec_o,NULL)!=0){
  perror("timer_settime");
  exit(EXIT_FAILURE);
}
int ret;
struct sched_param param;
int min_priority = sched_get_priority_min(SCHED_FIFO);

cpu_set_t cpuset;
CPU_ZERO(&cpuset);
CPU_SET(0, &cpuset);

pthread_attr_t attributs;

/*Pour duminuer la priorité du thread qu'on arrete, pour qu'il reprend pas son exécution à une date qu'on ne veut. Sa priorité devient plus petite que la priorité de la tâche idle*/
if((i_prec!=(-1))&&(i!=(-1))&&(Nb_threads[(T[i_prec].id-1)]) ){
	param.sched_priority = min_priority ;
	int ret=pthread_setschedparam(Nb_threads[(T[i_prec].id-1)],SCHED_FIFO, &param);
}

if(T[i].create_thread==1){

		pthread_attr_init(&attributs);
		/*affinité du thread crée*/
		if(pthread_attr_setaffinity_np(&attributs,sizeof(cpu_set_t),&cpuset)!=0)
  			printf ("erreur affinité \n");

		/*Algo d'ordonnancement FIFO avec priorité*/
		if(pthread_attr_setschedpolicy(&attributs,SCHED_FIFO)!=0){
			fprintf(stderr, "Modification de l'algo d'ordonnancement a echoué \n");
			 exit(EXIT_FAILURE);
		}

		/*Pour ne pas hériter d'un autre algo d'ordonnancement*/
		if(pthread_attr_setinheritsched(&attributs,PTHREAD_EXPLICIT_SCHED)!=0){
			fprintf(stderr, " Erreur héritage algo d'ordo 2\n");
 			exit(EXIT_FAILURE);
		}

		//struct sched_param param pour donner une priorité au thread;
		//int max_priority = sched_get_priority_max(SCHED_FIFO);
		param.sched_priority=98;
		if(pthread_attr_setschedparam(&attributs,&param)!=0){
 			fprintf(stderr, " erreurs priorité \n");
 			exit(EXIT_FAILURE);
		}

		/*Création du thread avec les paramètres in */
		if(pthread_create((Nb_threads+(T[i].id-1)),&attributs,(*T[i].code),NULL)!=0){
  		printf ("Erreur creation thread %d\n",T[i].id);
  		exit(EXIT_FAILURE);
 		}
}
/*Reprise d'exécution d'un thread. Dans ce cas on redonne au thread Nb_threads[(T[i].id-1)], la plus grande priorité */
else
if((Nb_threads[(T[i].id-1)])){
printf ("[%f]  reprise Task%d \n",(clock()/(double)CLOCKS_PER_SEC),T[i].id);
param.sched_priority = 98 ;
ret = pthread_setschedparam(Nb_threads[(T[i].id-1)],SCHED_FIFO,&param);
}

}



/****************/
/*Fonction main*/
int main (void){
int compteur=0;
int err;
cpu_set_t cpuset;
CPU_ZERO(&cpuset);
CPU_SET(0, &cpuset);

pthread_attr_t attributs;
struct sched_param param;
param.sched_priority=99;
// Affinité du thread main
if((sched_setaffinity(0,sizeof(cpu_set_t),&cpuset)!=0))
   printf ("Erreur affinity main \n");


if(sched_setscheduler(0,SCHED_FIFO,&param)!=0)
   printf ("Erreur setchedluer main \n");

/*Initialisation de la durée du timer*/
spec_o.it_value.tv_sec=0;
spec_o.it_value.tv_nsec=1;
spec_o.it_interval.tv_sec=0;
spec_o.it_interval.tv_nsec=0;

// Installer la routine du signal
signal(SIGRTMIN+1,ordonnanceur);
event_o.sigev_notify=SIGEV_SIGNAL;
event_o.sigev_signo=SIGRTMIN+1;

if(timer_create(CLOCK_REALTIME,&event_o,&timer_o)!=0){
  perror("timer_create");
  exit(EXIT_FAILURE);
  }

/* Création du thread pour la tâche idle Cette est une boubcle */

pthread_attr_init(&attributs);
///*
CPU_ZERO(&cpuset);
CPU_SET(0, &cpuset);

if( pthread_attr_setaffinity_np(&attributs,sizeof(cpu_set_t),&cpuset)!=0)
  printf ("erreur affinité \n");

if((err=pthread_attr_setschedpolicy(&attributs,SCHED_FIFO))!=0){
fprintf(stderr, "Modification de l'algo d'ordonnancement a echoué \n");
 exit(EXIT_FAILURE);
}

if((err=pthread_attr_setinheritsched(&attributs,PTHREAD_EXPLICIT_SCHED))!=0){
fprintf(stderr, " Erreur héritage algo d'ordo 2\n");
 exit(EXIT_FAILURE);
}

//struct sched_param param;
int min_priority = sched_get_priority_min(SCHED_FIFO);
param.sched_priority= (min_priority+1);

if((err=pthread_attr_setschedparam(&attributs,&param))!=0){
 fprintf(stderr, " erreurs priorité \n");
 exit(EXIT_FAILURE);
}
pthread_t thread_idle;

if((pthread_create(&thread_idle,&attributs,&idle,NULL)!=0) ){
  printf ("Erreur creation thread idle \n");
  exit(EXIT_FAILURE);
 }

/*Fin création thread de la tâche idle*/




//Armer le timer timer_o pour la première fois

if(timer_settime(timer_o,0,&spec_o,NULL)!=0){
  perror("timer_settime");
  exit(EXIT_FAILURE);
}





while (compteur < 200){

compteur++;

/*En attente de signal*/

pause();
}

return EXIT_SUCCESS;
}
