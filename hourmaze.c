/*
Autores:
    Alejandro Budiño Regueira   
    Manuel Couto Pintos
*/
#include <sys/stat.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <ctype.h>
#include <dirent.h>
#include <sys/types.h>
#include <errno.h>
#include <time.h>


#define H 12

int cell(int x, int y, int cols){ return (x*cols)+(y + 1); }

int row_from_cell(int c, int columns){ return (c-1)/columns;}

int col_from_cell(int c, int columns){ return (c-1)%columns;}

int cell_num(int cell, int num){ return (cell - 1)*H + num; }

int number_from_clasp(int n){
    return (n%H == 0)? H:n%H;
}

int cell_from_classp(int n){
    return ((n-number_from_clasp(n))/(H)+1);
}

// BINARY ADDITION RULES GENERATORS
void ADD (FILE * file, int a, int b, int sum, int carry, int *clauses){
    // Parte suma
    fprintf(file, "c XoR\n"); 
    fprintf(file, "c (A V B) & (-A V -B) -> S\n"); 
    fprintf(file, "-%d %d %d 0\n", a, b, sum); 
    fprintf(file, "-%d %d %d 0\n", b, a, sum);
    fprintf(file, "\n"); 

    fprintf(file, "c (A & B) V (-A & -B) -> -S\n"); 
    fprintf(file, "-%d -%d -%d 0\n", a, b, sum);
    fprintf(file, "%d %d -%d 0\n", a, b, sum);
    fprintf(file, "\n"); 
    
    // Parte carry
    fprintf(file, "c CARRY\n"); 
    fprintf(file, "c A & B -> C\n"); 
    fprintf(file, "-%d -%d %d 0\n\n", a, b, carry);
    fprintf(file, "\n"); 
    
    fprintf(file, "c -A V -B -> - C\n"); 
    fprintf(file, "%d -%d 0\n", a, carry);
    fprintf(file, "%d -%d 0\n", b, carry);
    fprintf(file, "\n"); 

    (*clauses)+=7;
}

void OR (FILE * file, int carry1, int carry2, int carry3, int *clauses){
    fprintf(file,"c OR \n");
    fprintf(file, "c C1 V C2 -> C3\n"); 
    fprintf(file, "-%d %d 0\n", carry1, carry3);
    fprintf(file, "-%d %d 0\n", carry2, carry3);
    fprintf(file, "%d %d -%d 0\n",carry1, carry2, carry3);
    fprintf(file, "\n"); 
    (*clauses)+=3;
}

void F_ADD (FILE *file, int a, int b, int c, int f_sum, int f_carry, int *last_var,  int *clauses){
    int sum1 = (*last_var)++;
    int carry1 = (*last_var)++;
    int carry2 = (*last_var)++;

    fprintf(file, "\n"); 
    fprintf(file,"c SUMADOR\n");
    ADD(file, a, b, sum1, carry1, clauses);
    ADD(file, sum1, c, f_sum, carry2, clauses); 
    OR(file, carry1, carry2, f_carry, clauses);
    fprintf(file,"c FIN SUMADOR\n\n\n");
}

// BINARY ADDITION END

int **matrix_alloc(int filas, int columnas){
    int **matrix; 
    
    matrix = (int**) malloc(filas * sizeof(int*));
    
    for (int i = 0; i<filas; i++) {
        matrix[i] = malloc(columnas*sizeof(int));
    }
    return matrix;
}

void matrix_dealloc(int **matrix, int filas){
   
    for(int i=0; i<filas; i++){
        free(matrix[i]);
    }
    free(matrix);
}

void matrixcopy (void *destmat, void *srcmat, int filas, int columnas){
  memcpy(destmat,srcmat, filas*columnas*sizeof(int));
}

void matrix_value_copy(int **destmat, int **srcmat, int filas, int columnas){
    int i,j;

    for(i=0; i<filas; i++){
        for(j=0; j<columnas; j++){
            destmat[i][j] = srcmat[i][j];
        }
    }
}

void set_counter_final_rules(FILE * file, int filas, int columnas, int* bit_array, int n_bits, int *clauses){
    int i = 0;
    int rep_bits[n_bits];
    int rep = filas*columnas/H;

    for(i=0; i<n_bits; i++){
        rep_bits[i] = 0;
    }

    for(i=0; rep>0; i++){
        rep_bits[i] = rep%2;
        rep=rep/2;
    }

    for(i=0; i<n_bits; i++){
        if(rep_bits[i]==1){
            fprintf(file,"%d 0\n",bit_array[i]);
        } else {
            fprintf(file,"-%d 0\n",bit_array[i]);
        }
    }

    (*clauses)+=3;
}


int *level_addition(FILE *file, int n_bits, int sum1[], int sum2[], int *clauses, int *last_var){
    int i;
    int new_carry, previous_carry;
    int *level_sum = malloc((n_bits)*sizeof(int));

    level_sum[0] = (*last_var)++;
    new_carry = (*last_var)++;
    fprintf(file, "c HALF ADD\n"); 
    ADD(file, sum1[0], sum2[0], level_sum[0], new_carry, clauses); 
    
    for(i=1; i<(n_bits-1); i++){
        previous_carry = new_carry;
        level_sum[i] = (*last_var)++;
        new_carry = (*last_var)++;
        F_ADD (file, sum1[i], sum2[i], previous_carry, level_sum[i], new_carry, last_var, clauses);
    }

    level_sum[(n_bits-1)] = new_carry;

    return level_sum;
}

void stepped_addition(FILE * file, int n, int filas, int columnas, int *clauses, int *last_var)
{
    int i; //iteradores
    int counter, previous_counter; // cuenta
    int a,b,c; //Variables de celda
    
    int n_bits = 2;

    int **addition_matrix;
    int **aux_matrix;
    
    //Procesamos 1º nivel 
    counter = 0;
    if(filas*columnas%3 == 0)
    {
        addition_matrix = matrix_alloc(filas*columnas/3, n_bits);
        for(i=1; i<=filas*columnas; i+=3){
            a = cell_num(i,n);
            b = cell_num(i+1,n);
            c = cell_num(i+2,n);
            addition_matrix[counter][0] = (*last_var)++;
            addition_matrix[counter][1] = (*last_var)++; 
            
            F_ADD(file, a, b, c, addition_matrix[counter][0], addition_matrix[counter][1], last_var, clauses);
            counter++;
        }

    } else 
    {
        addition_matrix = matrix_alloc(filas*columnas/2, n_bits);
        for(i=1; i<=filas*columnas; i+=2){
            addition_matrix[counter][0] = (*last_var)++;
            addition_matrix[counter][1] = (*last_var)++;
            a = cell_num(i,n);
            b = cell_num(i+1,n);
            ADD(file, a, b, addition_matrix[counter][0], addition_matrix[counter][1], clauses);
            counter++;
        }
    }
    
    while((previous_counter=counter) > 1)
    {
        // Esto funciona para un número de casillas cuya descomposición factorial tenga máximo 2 treses
        // Para que funciones con mayor número de múltiplos de 3 habría que ver que mientras fuera multiplo de 2
        // se ejecutara las actuales cláusulas del else y cuando ya no quedaran más comenzar a ejecutar la parte del
        // actual if.  
        if(previous_counter == 3){ 
            n_bits++;
            counter = 1;
            aux_matrix = (int **) malloc(2 * sizeof(int *));
            aux_matrix[1] = malloc(n_bits * sizeof(int));
            aux_matrix[0] = level_addition(file, n_bits, addition_matrix[0], addition_matrix[1], clauses, last_var);
            
            for(int j=0; j<n_bits-1; j++){
                aux_matrix[1][j] = addition_matrix[2][j];
            }
            aux_matrix[1][n_bits-1] = (*last_var)++;
            fprintf(file, "-%d 0\n", (*last_var)-1);

            n_bits++; // TRUCO QUE NO CUBRE TODAS LAS PÔSIBLIDADES, SI OVERFLOW ROMPE
            matrix_dealloc(addition_matrix, previous_counter);
            addition_matrix = (int **)malloc(1*sizeof(int *));
            addition_matrix[0] = level_addition(file, n_bits, aux_matrix[0], aux_matrix[1], clauses, last_var);
            matrix_dealloc(aux_matrix, counter);

        } else {
            n_bits++;
            aux_matrix = (int **)malloc((previous_counter/2)*sizeof(int *));

            counter = 0;
            for(i=0; i<(previous_counter); i+=2){
                aux_matrix[counter] = level_addition(file, n_bits, addition_matrix[i], addition_matrix[i+1], clauses, last_var);
                counter++;
            }
            //Memory management
            matrix_dealloc(addition_matrix, previous_counter);
            addition_matrix = matrix_alloc(counter, n_bits);
            matrix_value_copy(addition_matrix, aux_matrix, counter, n_bits);
            matrix_dealloc(aux_matrix, counter);
        }
        
    }
    
    set_counter_final_rules(file, filas, columnas, addition_matrix[0], n_bits, clauses);
    matrix_dealloc(addition_matrix, 1);
}

void reglas_horas_derecha(FILE *file, int columnas, int i, int j, int n, int *clauses)
{
    int k=0;

    //Para un número qué no puede haber en la casilla de la derecha
    fprintf(file,"c REGLAS DERECHA \n");
    fprintf(file, "-%d ", cell_num(cell(i,j/2,columnas),n)); 
    for(k=1; k<=H; k++){
        if((k%H) != ((n+1)%H) && (k%H) != ((n-1)%H)){
            fprintf(file, "-%d ",cell_num(cell(i,(j/2)+1,columnas),k));
        } 
    }
    fprintf(file, "0\n");
    (*clauses)++;

    //Para un número, qué puede haber en la casilla de la derecha
    
    fprintf(file, "-%d ", cell_num(cell(i,j/2,columnas),n)); 
    for(k=1; k<=H; k++){
        if((k%H) == ((n+1)%H) || (k%H) == ((n-1)%H))
        {
            fprintf(file, "%d ",cell_num(cell(i,(j/2)+1,columnas),k));
        } 
    }
    fprintf(file, "0\n");
    (*clauses)++;
    
}

void reglas_horas_abajo(FILE *file, int columnas, int i, int j, int n, int *clauses)
{
    int k=0;
    
    fprintf(file,"c REGLAS ABAJO \n");
    //Para un número qué no puede haber en la casilla de abajo
    fprintf(file, "-%d ", cell_num(cell(i,j/2,columnas),n));
    for(k=1; k<=H;k++){
        if(((k)%H) != ((n+1)%H) && ((k)%H) != ((n-1)%H)){
            fprintf(file, "-%d ",cell_num(cell(i+1,j/2,columnas),k));
        }
    }
    fprintf(file, "0\n");
    (*clauses)++;

    //Para un número qué puede haber en la casilla de abajo
    
    fprintf(file, "-%d ", cell_num(cell(i,j/2,columnas),n));
    for(k=1; k<=H;k++){
        if(((k)%H) == ((n+1)%H) || ((k)%H) == ((n-1)%H)){
            fprintf(file, "%d ",cell_num(cell(i+1,j/2,columnas),k));
        }
    }

    fprintf(file, "0\n");
    (*clauses)++;
    
}

void regla_hora_en_celda(FILE *file, int filas, int columnas, int i, int j, int n, char buffer[], char buffer2[], int top, int *clauses){
    int k=0;

    fprintf(file, "c sabemos que %d en celda %d\n",n ,cell_num(n, cell(i,j/2,columnas)));
    fprintf(file, "%d 0\n", cell_num(cell(i,j/2,columnas),n)); 
    (*clauses)++;

    //Reglas arriba
    /*
    if(top){
        for(k=1; k<=H;k++){
            if(((k)%H) != ((n+1)%H) && ((k)%H) != ((n-1)%H)){
                fprintf(file, "-%d 0\n",cell_num(cell(i-1,j/2,columnas),k));
                (*clauses)++;
            }
        }
    }*/

    //Reglas abajo
    if((i<(filas-1)) && buffer2[j]!='-'){
        for(k=1; k<=H;k++){
            if(((k)%H) != ((n+1)%H) && ((k)%H) != ((n-1)%H)){
                fprintf(file, "-%d 0\n",cell_num(cell(i+1,j/2,columnas),k));
                (*clauses)++;
            }
        }
    }
    //Reglas derecha
    if((j/2)<(columnas-1) && buffer[j+1]!='|'){
        for(k=1; k<=H; k++){
            if((k%H) != ((n+1)%H) && (k%H) != ((n-1)%H)){
                fprintf(file, "-%d 0\n",cell_num(cell(i,(j/2)+1,columnas),k));
                (*clauses)++;
            } 
        }
    }
    //Reglas izquierda
    if((j)>0 && buffer[j-1]!='|'){
        for(k=1; k<=H; k++){
            if((k%H) != ((n+1)%H) && (k%H) != ((n-1)%H)){
                fprintf(file, "-%d 0\n",cell_num(cell(i,(j/2)-1,columnas),k));
                (*clauses)++;
            } 
        }
    }
}

FILE *get_problem_head(char *filename, int *filas, int *columnas){
    
    FILE *fp;
    char buffer[100];
    
    // Open and Read FILE
    printf("* %s -----------------------------------------------------\n\n",filename);
    fp = fopen(filename,"r");

    if (fp != NULL) 
    {
        printf(" * PROBLEM HEAD:\n");
        //(*columnas)
        fgets(buffer, 100, fp);
        (*columnas) = atoi(buffer);
        printf("\tcolumnas -> %d \n", (*columnas));

        //(*filas)
        fgets(buffer, 100, fp);
        (*filas) = atoi(buffer);
        printf("\tfilas -> %d \n", (*filas));

    }
    printf("\n");

    return fp;

}

char **process_problem(FILE *fp, FILE *file, int filas, int columnas, int *clauses){
    
    char **matrix = (char**)malloc(filas * 2 * sizeof(char *));
    //int processed_cells[filas][columnas];

    for(int i=0; i<(filas*2); i++)
        matrix[i] = malloc(columnas * 2 * sizeof(char));

    for(int i=0; i<(filas*2); i++)
        for(int j=0; j<(columnas*2); j++){
            matrix[i][j]='\0';
        }

    if (fp != NULL) {
        int i, j, n;
        char buffer[100];
        char buffer2[100];

        printf(" * IMPUT MAP:\n");

        fprintf(file,"\n");

        // Procesar La entrada
        i=0;
        while (fgets(buffer, sizeof buffer, fp) != NULL) {

            if(i<(filas-1)){
                fgets(buffer2, sizeof buffer2, fp);
            } else {
                buffer2[0]='\0';
            }

            for(j=0; buffer[j]!='\0'; j++){
                
                matrix[i*2][j] = buffer[j];
                if(i<(filas-1))
                    matrix[(i*2)+1][j] = buffer2[j];

                if((j%2)==0){

                    fprintf(file,"\n \nc Poniendo reglas a celda (%d,%d)\n",i,j/2);

                    if(isxdigit(buffer[j])){
                        n = strtol((char[]){buffer[j], 0}, NULL, 16);
                        if(n<=H){
                            if(i>0 && matrix[((i-1)*2)+1][j]!='-'){
                                regla_hora_en_celda(file, filas, columnas, i, j, n, buffer, buffer2, 1, clauses);
                            } else {
                                regla_hora_en_celda(file, filas, columnas, i, j, n, buffer, buffer2, 0, clauses);
                            }
                            
                            fprintf(file, "\n\n");
                        } else {
                            perror("Invalid Number\n");
                        }
                    } else {
                        for(n=1; n<=H;n++){
                            if((j/2)<(columnas-1) && buffer[j+1]!='|'){
                                reglas_horas_derecha(file, columnas, i, j, n, clauses);
                            }
                            
                            if((i<(filas-1)) && buffer2[j]!='-'){
                                reglas_horas_abajo(file, columnas, i, j, n, clauses);
                            }
                            fprintf(file, "\n\n");
                        }
                    }
                }
            }

            printf("\t%s", buffer);
            printf("\t%s", buffer2);
            i++;
        }

        printf("\n\n");
    }

    return matrix;
}

char **read_result(char *fileName, int filas, int columnas){
    int c,i;
    FILE *file;
    char **board;
    int t = 0;
    int fila, columna, number, cell;

    board = (char**) malloc((filas) * sizeof(char *));
    for(i=0; i<filas; i++)
        board[i] = malloc(columnas * sizeof(char));


    file = fopen("result.txt","r");

    if((c=fgetc(file))==EOF || c!='v') exit(1);

    char aux[4];
    while((c=fscanf(file,"%d ", &t))!=EOF){
        if(c==0){
            fgetc(file); continue;
        }else if(t > 0 && t <= filas * columnas * H){
            cell = cell_from_classp(t);
            fila = row_from_cell(cell,columnas);
            columna = col_from_cell(cell,columnas);
            number = number_from_clasp(t);
            sprintf(&aux[0],"%X",(number%H == 0)?H:number%H);
            board[fila][columna] = aux[0];
        }
    }

    fclose(file);

    printf("\n");

    return board;
}

void print_result(int filas, int columnas, char **board, char **matrix){
    int i = 0, j = 0;
    char aux = '\0';

    printf("RESULT MAP:\n");
    for(i=0; i<filas; i++){
        printf("\t");
        for(j=0; j<columnas; j++){
            aux = matrix[(i*2)][(j*2)+1];
            printf("%c%c", board[i][j],((aux=='|')?'|':' '));
        }
        printf("\n\t");
        if((i+1)<filas){
            for(j=0; j<columnas; j++){
                aux = matrix[(i*2)+1][(j*2)];
                printf("%c ",aux);
            }
            printf("\n");
        }
    }
    printf("\n");
}

void hourmaze(char *filePath){
    char **matrix;
    char **board;
    FILE * file;
    FILE * fp;

    struct timespec ts1, ts2;
    
    int n,i,j;

    int filas = 0;
    int columnas = 0;
    int clauses = 0;
    int last_var = 0;

    fp = get_problem_head(filePath, &filas, &columnas);
    file = fopen("clauses.txt","w");
    matrix = process_problem(fp, file, filas, columnas, &clauses);
    last_var = filas * columnas * H + 1;

    for(n=1; n<=H; n++){
        fprintf(file,"\n");
        fprintf(file,"c SUMADOR Para el número -> (%d) \n", n);
        stepped_addition(file, n, filas, columnas, &clauses, &last_var);
    } 

    //Almenos un número en cada casilla
    fprintf(file, "c ALMENOS OCUPAMOS CADA CASILLA\n");
    for(i=0; i<filas; i++){
        for(j=0; j<columnas; j++){
            fprintf(file, "c La casilla (%d,%d) tendrá almenos 1 número \n",i,j);
            for(n=1; n<=(H);n++){
                fprintf(file, "%d ",cell_num(cell(i,j,columnas),n));
            }                    
            fprintf(file, "0\n");
            clauses++;
        }
    }

    for(n=1; n<=(H);n++){
        fprintf(file, "c El numero %d almenos en una casilla \n",n);
        for(i=0; i<filas; i++){
            for(j=0; j<columnas; j++){
                fprintf(file, "%d ",cell_num(cell(i,j,columnas),n));
            }
        }
        fprintf(file, "0\n");
        clauses++;
    }

    printf(" * Clausulas > %d \n", clauses);

    printf(" * Variables > %d \n", last_var);

    fclose(fp);

    fclose(file);

    file = fopen("satfile.txt","w");

    fprintf(file,"p cnf %d %d \n", last_var, clauses);

    fclose(file);

    system("cat clauses.txt >> satfile.txt");

    clock_gettime( CLOCK_REALTIME, &ts1 );

    system("clasp --verbose=0 satfile.txt > result.txt");

    clock_gettime( CLOCK_REALTIME, &ts2 );

    printf(" * Tiempo de ejecucion(clasp): %f\n", 
        (float) ( 1.0*(1.0*ts2.tv_nsec - ts1.tv_nsec*1.0)*1e-9 + 1.0*ts2.tv_sec - 1.0*ts1.tv_sec )/60 );

    board = read_result("examples/dom01.txt", filas, columnas);

    print_result(filas, columnas, board, matrix);

    printf("\n");

    // Free dynamic memory
    for(int i=0; i<(filas*2); i++)
        free(matrix[i]);

    for(int i=0; i<filas; i++)
        free(board[i]);

    free(matrix);
    free(board);
}

int is_regular_file(const char *path)
{
    struct stat path_stat;
    stat(path, &path_stat);
    return S_ISREG(path_stat.st_mode);
}

int main(int argc, char *argv[]) 
{
    int i;
    DIR *dir;
    struct dirent *ent;
    char filePath[100];

    for(i=1; i<argc; i++)
    {
        if(is_regular_file(argv[i]))
        {
            printf("regular_FILE\n");
            hourmaze(argv[i]);
        } else {
            printf("DIR > %s \n",argv[i]);
            dir = opendir(argv[i]);

            if(dir == NULL)
                perror("No puedo abrir el directorio");

            while ((ent = readdir (dir)) != NULL)
            {
                if ( (strcmp(ent->d_name, ".")!=0) && (strcmp(ent->d_name, "..")!=0) )
                {
                    strcpy(filePath, argv[i]);
                    strcat(filePath, "/");
                    strcat(filePath, ent->d_name);
                    hourmaze(filePath);
                }
            }
        }
    }

    

    return 0;
}
