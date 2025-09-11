#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdatomic.h>
#include <genmc.h>

atomic_int a;
atomic_int b;
atomic_int c;

void __VERIFIER_assume(int);

void *thread_1(void *unused)
{
	atomic_store_explicit(&c, 1, memory_order_seq_cst);
	atomic_store_explicit(&a, 1, memory_order_seq_cst);
	int b_local = atomic_load_explicit(&b, memory_order_seq_cst);
	__VERIFIER_assume(b_local == 2);
	return NULL;
}

void *thread_2(void *unused)
{
	atomic_store_explicit(&b, 2, memory_order_seq_cst);
	atomic_store_explicit(&a, 3, memory_order_seq_cst);
	int c_local = atomic_load_explicit(&c, memory_order_seq_cst);
	__VERIFIER_assume(c_local == 1);
	return NULL;
}

void *thread_3(void *unused)
{
	atomic_store_explicit(&c, 3, memory_order_seq_cst);
	int a_local = atomic_load_explicit(&a, memory_order_seq_cst);
	int b_local = atomic_load_explicit(&b, memory_order_seq_cst);
	__VERIFIER_assume(a_local == 1);
	__VERIFIER_assume(b_local == 4);
	return NULL;
}

void *thread_4(void *unused)
{
	atomic_store_explicit(&b, 4, memory_order_seq_cst);
	int a_local = atomic_load_explicit(&a, memory_order_seq_cst);
	int c_local = atomic_load_explicit(&c, memory_order_seq_cst);
	__VERIFIER_assume(a_local == 2);
	__VERIFIER_assume(c_local == 3);
	return NULL;
}


int main()
{
	pthread_t t1, t2, t3, t4;

	if (pthread_create(&t1, NULL, thread_1, NULL))
		abort();
	if (pthread_create(&t2, NULL, thread_2, NULL))
		abort();
	if (pthread_create(&t3, NULL, thread_3, NULL))
		abort();
	if (pthread_create(&t4, NULL, thread_4, NULL))
		abort();

	
	return 0;
}
