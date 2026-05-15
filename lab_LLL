#include <iostream>
#include <vector>
#include <random>

using namespace std;

static const int RANK = 30;

class LLL{

private:
    int matrix[RANK][RANK];
    float delta;

public:
    void Generate_Matrix(){
        const int LIMIT = 50000;
        static mt19937_64 rng(random_device{}());
        uniform_int_distribution<int32_t> dist(-LIMIT, LIMIT);
        for (int i = 0; i < RANK; i++){
            for (int j = 0; j < RANK; j++){
                matrix[i][j] = dist(rng);
            }
        }
    }

    LLL(float d){
        if (d < 0.25 || d > 1) {cerr << "Invalid parameter."; exit(1);}
        Generate_Matrix();
    }





};


using namespace std;

int main()
{

    for (int i = 0; i < 50; i++){
        LLL M(0.5);
    }


    return 0;
}
