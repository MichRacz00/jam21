#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdatomic.h>
#include <genmc.h>

atomic_int x;
atomic_int y;

void __VERIFIER_assume(int);

void *thread_1(void *unused)
{
	atomic_store_explicit(&x, 7, memory_order_release);
	atomic_store_explicit(&y, 3, memory_order_release);
	return NULL;
}

void *thread_2(void *unused)
{
	atomic_load_explicit(&y, memory_order_acquire);
	atomic_load_explicit(&x, memory_order_acquire);
	return NULL;
}


int main()
{
	pthread_t t1, t2;

	if (pthread_create(&t1, NULL, thread_1, NULL))
		abort();
	if (pthread_create(&t2, NULL, thread_2, NULL))
		abort();
	
	return 0;
}
