#ifndef DATASET_H_
#define DATASET_H_


#define M 8
#define N 8
#define NNZ 6

static const int32_t A_data[6] = { -2, -3, -4, 1, -3, -4 };

static const int32_t A_indices[6] = { 7, 1, 2, 3, 4, 7 };

static const int32_t A_indptr[9] = { 0, 0, 1, 2, 2, 2, 2, 3, 6 };

static const int32_t invcol_index[6] = { 2, 6, 7, 7, 1, 7 };

static const int32_t s_index[9] = { 0, 0, 1, 2, 3, 4, 4, 4, 6 };

static const int32_t x[8] = { -4, -3, 3, 3, 1, 1, -3, 4 };

#endif /* DATASET_H_ */
