#ifndef IXS_LIMITS_H_
#define IXS_LIMITS_H_

/*
 * Maximum number of terms in an ADD/MUL/AND/OR/PIECEWISE node.
 * Kept small to avoid blowing the stack in recursive rewrite passes
 * (each smart constructor allocates MAX_TERMS-sized arrays on the stack).
 */
#define MAX_TERMS 256

#endif /* IXS_LIMITS_H_ */
