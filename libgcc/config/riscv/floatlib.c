#ifdef __gap9__

/* Convert half to double */
double __extendhfdf2 (float16 a1)

{
        register float F;
        __asm ("fcvt.s.h %0, %1" : "=r" (F) : "r" (a1) );
        return F;
}

/* */

/* Convert alternative half to double */
double __extendohfdf2 (float16alt a1)

{
	float F;
	__asm ("fcvt.s.ah %0, %1" : "=r" (F) : "r" (a1) );
	return F;
}


/* Truncate double to half*/
float16 __truncdfhf2 (double a1)

{
	register float F = a1;
	float16 R;
	__asm ("fcvt.h.s %0, %1" : "=r" (R) : "r" (F) );
	return R;

}

/* Truncate double to alternative half*/
float16alt __truncdfohf2 (double a1)

{
	register float F = a1;
	float16alt R;
	__asm ("fcvt.ah.s %0, %1" : "=r" (R) : "r" (F) );
	return R;

}

#endif
