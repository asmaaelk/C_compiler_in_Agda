#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  int tag;
  void *p1;
  void *p2;
} pair;

typedef struct {
  int tag;
  char cs;
} str;

#define PAIR 0
#define STR 1

pair *newpair(void *p1, void *p2) {
  pair *p = (pair *)malloc(sizeof(pair));
  p->tag = PAIR;
  p->p1 = p1;
  p->p2 = p2;
  return p;
}

str *newstr(char *cs) {
  int len = strlen(cs);
  int sz = sizeof(int) + (4*(len+1))/4;
  str *s = (str *)malloc(sz);
  s->tag = STR;
  strcpy(&s->cs,cs);
  return s;
}

void printh(void *x) {
  if (*((int *)x) == PAIR) {
    // it is a pair
    pair *p = (pair *)x;
    printf("[");
    printh(p->p1);
    printf(",");
    printh(p->p2);
    printf("]");
  }
  else {
    // it is a string
    str *s = (str *)x;
    printf("\"");
    fputs(&s->cs, stdout);
    printf("\"");
  }
}

int print(void *x) {
  printh(x);
  printf("\n");
  return 0;
}

void *convert(int argc, char **argv) {
  int i;
  void **r = (void **)0;
  for (i = argc - 1; i > 0; i--) {
    if (!r) 
      r = newstr(argv[i]);
    else
      r = newpair(newstr(argv[i]),r);
  }
  if (!r)
    r = newstr("");
  return r;
}

int labort() {
  exit(1);
  return 0;
}

void *_main(void *x0) {
_start__main: {void *args = x0;
return args;
}
}
void *main(void *argc,void *argv) {
return print(_main(convert(argc , argv)));
}
