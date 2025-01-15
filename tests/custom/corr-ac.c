#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdatomic.h>
#include <genmc.h>

atomic_int n;
atomic_int i;

void *thread_1(void *unused)
{
	atomic_store_explicit(&n, 1, memory_order_seq_cst);
	atomic_load_explicit(&n, memory_order_seq_cst);
	atomic_load_explicit(&n, memory_order_seq_cst);
	//while(atomic_load_explicit(&n, memory_order_relaxed) != 9);
	//atomic_store_explicit(&n, 2, memory_order_seq_cst);
	return NULL;
}

void *thread_2(void *unused)
{
	atomic_store_explicit(&n, 1, memory_order_seq_cst);
	atomic_load_explicit(&n, memory_order_seq_cst);
	atomic_load_explicit(&n, memory_order_seq_cst);
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
