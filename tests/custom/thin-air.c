#include <stdio.h>
#include <stdatomic.h>
#include <pthread.h>

atomic_int x = 0;
atomic_int y = 0;

void *thread1(void *arg) {
	atomic_load_explicit(&y, memory_order_relaxed);
    atomic_store_explicit(&x, 1, memory_order_relaxed);
    return NULL;
}

void *thread2(void *arg) {
	atomic_load_explicit(&x, memory_order_relaxed);
    atomic_store_explicit(&y, 1, memory_order_relaxed);
    return NULL;
}

int main() {
    pthread_t t1, t2;

    pthread_create(&t1, NULL, thread1, NULL);
    pthread_create(&t2, NULL, thread2, NULL);

    pthread_join(t1, NULL);
    pthread_join(t2, NULL);

    return 0;
}
