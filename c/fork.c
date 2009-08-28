
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>

fork1(){
  pid_t pid;
  int rv;
  switch(pid=fork()) {case -1:perror("fork");  
      /* something went wrong */
      exit(1);         
      /* parent exits */
  case 0:
    sleep(1);
    printf(" CHILD: This is the child process!\n");
    printf(" CHILD: My PID is %d\n", getpid());
    printf(" CHILD: My parent's PID is %d\n", getppid());
    printf(" CHILD: Enter my exit status (make it small): ");
    scanf(" %d", &rv);
    printf(" CHILD: I'm outta here!\n");
    exit(rv);
  default:
    printf("PARENT: This is the parent process!\n");
    printf("PARENT: My PID is %d\n", getpid());
    printf("PARENT: My child's PID is %d\n", pid);
    printf("PARENT: I'm now waiting for my child to exit()...\n");
    wait(&rv);
    sleep(1);
    printf("PARENT: My child's exit status is: %d\n", WEXITSTATUS(rv));
    printf("PARENT: I'm outta here!\n");
  }
}

fork2() {
  pid_t pid;

  if (pid=fork() == -1) perror("fork");
  int i=0;
  if (pid == 0) 
    {
      for (i=0; i<1; i++){
	printf("  hi, my id is %d\n", pid);
	printf("  hi, my get pid is %d\n", getpid());
	printf("  hi, my get ppid is %d\n", getppid());
      }
    }
  else 
    {
      for (i=0; i<1; i++) {
	printf("my id is %d\n", pid);
	printf("my get pid is %d\n", getpid());
	printf("my get ppid is %d\n", getppid());
      }
    }
}


int inc(int a){
  return a+1;
}

fork3() {
  pid_t pid; 
  pid = fork();
  int i = 0;
  while (i  < 5) {
    
    if (pid == 0 ) pid = fork();
    
    
      {
	i++;
	printf("%d + my pid is %d\n", i, getpid());   
      }
  }


}

/*
 * 一个方程用来增加变量；
 另外一个方程用来判断是否增加变量。
 */

fork4() {
  pid_t pid;
  int* pint = malloc(sizeof(int));
  *pint = 0;
  while (*pint < 5) {
    pid = fork();
  
    
    if (pid > 0) {
      
      *pint = *pint + 10;
      printf("%d  ", pint);
      printf("%d + my pid is %d\n", *pint, getpid());
    }

    else if (pid ==0) {
      *pint = *pint + 1;
      printf("%d  ", pint);
      printf("%d + my pid is %d\n", *pint, getpid());
    }
  }
}


main() {
  fork4();
}
