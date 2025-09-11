#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdatomic.h>
#include <genmc.h>

atomic_int x;

void *thread_1(void *unused)
{
	atomic_store_explicit(&x, 1, memory_order_seq_cst);
	atomic_store_explicit(&x, 1, memory_order_relaxed);
	atomic_store_explicit(&x, 1, memory_order_relaxed);
	atomic_store_explicit(&x, 1, memory_order_relaxed);
	atomic_store_explicit(&x, 1, memory_order_seq_cst);
	atomic_thread_fence(memory_order_seq_cst);
	atomic_store_explicit(&x, 1, memory_order_seq_cst);
	atomic_thread_fence(memory_order_seq_cst);
	atomic_store_explicit(&x, 1, memory_order_relaxed);
	atomic_store_explicit(&x, 1, memory_order_relaxed);
	atomic_store_explicit(&x, 1, memory_order_relaxed);
	atomic_thread_fence(memory_order_seq_cst);
	atomic_store_explicit(&x, 1, memory_order_seq_cst);
	return NULL;
}


int main()
{
	pthread_t t1;

	if (pthread_create(&t1, NULL, thread_1, NULL))
		abort();

	
	return 0;
}
