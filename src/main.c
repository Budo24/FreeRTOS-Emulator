#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <stdbool.h>
#include <string.h>


#include <SDL2/SDL_scancode.h>
#include "FreeRTOS.h"
#include "queue.h"
#include "semphr.h"
#include "task.h"
#include "timers.h"
#include "portmacro.h"

#include "TUM_Ball.h"
#include "TUM_Draw.h"
#include "TUM_Font.h"
#include "TUM_Event.h"
#include "TUM_Sound.h"
#include "TUM_Utils.h"
#include "TUM_FreeRTOS_Utils.h"
#include "TUM_Print.h"
#include "AsyncIO.h"

#define mainGENERIC_PRIORITY (tskIDLE_PRIORITY)
#define mainGENERIC_STACK_SIZE ((unsigned short)2560)

#define STATE_QUEUE_LENGTH 1

#define STATE_COUNT 3

#define STATE_ONE 0
#define STATE_TWO 1
#define STATE_THREE 2

#define NEXT_TASK 0
#define PREV_TASK 1

#define STARTING_STATE STATE_ONE

#define STATE_DEBOUNCE_DELAY 300

#define KEYCODE(CHAR) SDL_SCANCODE_##CHAR
#define CAVE_SIZE_X SCREEN_WIDTH / 2
#define CAVE_SIZE_Y SCREEN_HEIGHT / 2
#define CAVE_X CAVE_SIZE_X / 2
#define CAVE_Y CAVE_SIZE_Y / 2
#define CAVE_THICKNESS 25
#define LOGO_FILENAME "freertos.jpg"
#define MONSTER1 "monster1.jpg"
#define MONSTER2 "monster2.jpg"
#define MONSTER3 "monster3.jpg"
#define MOTHER "mother.jpg"

#define UDP_BUFFER_SIZE 1024
#define UDP_TEST_PORT_1 1234
#define UDP_TEST_PORT_2 1235
#define MSG_QUEUE_BUFFER_SIZE 1000
#define MSG_QUEUE_MAX_MSG_COUNT 10
#define TCP_BUFFER_SIZE 2000
#define TCP_TEST_PORT 2222


//my_constante
#define radius1 100
#define coordinate_origin SCREEN_WIDTH/2
#define PI 3.14

#define FPS_AVERAGE_COUNT 50
#define FPS_FONT "IBMPlexSans-Bold.ttf"
#define PRINT_TASK_ERROR(task) PRINT_ERROR("Failed to print task ##task");

const unsigned char next_state_signal = NEXT_TASK;
const unsigned char prev_state_signal = PREV_TASK;

static TaskHandle_t BufferSwap = NULL;
static TaskHandle_t positions = NULL;
static TaskHandle_t draw_everything = NULL;
static TaskHandle_t move_player_right = NULL;
static TaskHandle_t my_Substract = NULL;
static TaskHandle_t help_to_positions_of_enemy = NULL;
static TaskHandle_t bullet_of_player_task = NULL;
static TaskHandle_t enemy_bullet = NULL;
static TaskHandle_t mothership = NULL;
static TaskHandle_t mothership_on_off = NULL;
static TaskHandle_t show_text_dead_player = NULL;
static TaskHandle_t show_next_level = NULL;
static TaskHandle_t control_Multiplayer = NULL;
static TaskHandle_t mothership_multiplayer = NULL;


static QueueHandle_t StateQueue = NULL;
static QueueHandle_t Movement = NULL;

static QueueHandle_t X_player = NULL;
static QueueHandle_t Bullet_active = NULL;
static QueueHandle_t Difficulty = NULL;
static QueueHandle_t Pause_Resumed = NULL;
static QueueHandle_t Mothership_UDP = NULL;





static SemaphoreHandle_t DrawSignal = NULL;
static SemaphoreHandle_t ScreenLock = NULL;
static SemaphoreHandle_t HandleUDP = NULL;
aIO_handle_t udp_soc_receive = NULL, udp_soc_transmit = NULL;

static image_handle_t monster1 = NULL;
static image_handle_t monster2 = NULL;
static image_handle_t monster3 = NULL;
static image_handle_t mother = NULL;



//Hier are all global variables, locked in mutex(in main)

typedef struct my_values {
    int change_position;
    int seconds;
    int five;
    int y;
    int right;
    int left;
    int level;
    int score;
    int highscore;
    int live;
    int speed;
    int killed_enemies;
    int game_over;
    int pressed_replay;
    int pressed_pause;
    int not_use;
    int give_new_values;
    int give_new_replay;
    int highscore_multiplayer;
    bool multiplay_game;
    bool break_show_text_dead_player;
    SemaphoreHandle_t lock;
} my_values_t;

static my_values_t my_global_values = { 0 };
static my_values_t just_for_show_text_dead_player = {0};

//Used just few times


//

typedef struct buttons_buffer {
    unsigned char buttons[SDL_NUM_SCANCODES];
    SemaphoreHandle_t lock;
} buttons_buffer_t;

static buttons_buffer_t buttons = { 0 };

typedef struct enemies_position {
    int x_pixel;
    int y_pixel;
    int dead;
} enemies_position_t;

typedef struct enemy {
    enemies_position_t enemy_position[5][8];
    SemaphoreHandle_t lock;
} enemy_t;

typedef struct mother {
    enemies_position_t mothership;
    int collision_happend;
    bool multiplay_game;
    SemaphoreHandle_t lock;
} mother_t;

static enemy_t enemies = {0};

typedef struct player {
    int x_pixel_of_player;
    int y_pixel_of_player;
    int dead_of_player;
    int bullet_on_off;
    int position_take;
    int break_show_text_dead_player;
    SemaphoreHandle_t lock;
} player_t;



static player_t player1 = { 0 };

typedef struct bullet_player {
    int x_pixel_of_bullet;
    int y_pixel_of_bullet;
    int bullet_on;
    int collision_happend;
    int dead_player;
    int position_take;
    SemaphoreHandle_t lock;
} bullet_player_t;

typedef enum {HALT = 0, INC = 1, DEC = -1}
opponent_cmd_t;

static bullet_player_t bullet_of_player = { 0 };
static bullet_player_t bullet_of_enemy = { 0 };
static mother_t mothership_enemy = { 0 };

typedef struct blocks_position {
    int x_pixel_of_block;
    int y_pixel_of_block;
    int block_off;
} blocks_position_t;

typedef struct complete_blocks {
    blocks_position_t blocks_blocks[2][20];
    SemaphoreHandle_t lock;
} complete_blocks_t;

static complete_blocks_t green_blocks = {0};

void vApplicationGetIdleTaskMemory(StaticTask_t **ppxIdleTaskTCBBuffer,
                                   StackType_t **ppxIdleTaskStackBuffer,
                                   uint32_t *pulIdleTaskStackSize)
{
    /* If the buffers to be provided to the Idle task are declared inside this
    function then they must be declared static – otherwise they will be allocated on
    the stack and so not exists after this function exits. */
    static StaticTask_t xIdleTaskTCB;
    static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];

    /* Pass out a pointer to the StaticTask_t structure in which the Idle task’s
    state will be stored. */
    *ppxIdleTaskTCBBuffer = &xIdleTaskTCB;

    /* Pass out the array that will be used as the Idle task’s stack. */
    *ppxIdleTaskStackBuffer = uxIdleTaskStack;

    /* Pass out the size of the array pointed to by *ppxIdleTaskStackBuffer.
    Note that, as the array is necessarily of type StackType_t,
    configMINIMAL_STACK_SIZE is specified in words, not bytes. */
    *pulIdleTaskStackSize = configMINIMAL_STACK_SIZE;
}

/* configSUPPORT_STATIC_ALLOCATION and configUSE_TIMERS are both set to 1, so the
application must provide an implementation of vApplicationGetTimerTaskMemory()
to provide the memory that is used by the Timer service task. */
void vApplicationGetTimerTaskMemory(StaticTask_t **ppxTimerTaskTCBBuffer,
                                    StackType_t **ppxTimerTaskStackBuffer,
                                    uint32_t *pulTimerTaskStackSize)
{
    /* If the buffers to be provided to the Timer task are declared inside this
    function then they must be declared static – otherwise they will be allocated on
    the stack and so not exists after this function exits. */
    static StaticTask_t xTimerTaskTCB;
    static StackType_t uxTimerTaskStack[ configTIMER_TASK_STACK_DEPTH ];

    /* Pass out a pointer to the StaticTask_t structure in which the Timer
    task’s state will be stored. */
    *ppxTimerTaskTCBBuffer = &xTimerTaskTCB;

    /* Pass out the array that will be used as the Timer task’s stack. */
    *ppxTimerTaskStackBuffer = uxTimerTaskStack;

    /* Pass out the size of the array pointed to by *ppxTimerTaskStackBuffer.
    Note that, as the array is necessarily of type StackType_t,
    configTIMER_TASK_STACK_DEPTH is specified in words, not bytes. */
    *pulTimerTaskStackSize = configTIMER_TASK_STACK_DEPTH;
}







void UDPHandler(size_t read_size, char *buffer, void *args)
{
    opponent_cmd_t move = HALT;
    BaseType_t xHigherPriorityTaskWoken1 = pdFALSE;
    BaseType_t xHigherPriorityTaskWoken2 = pdFALSE;
    BaseType_t xHigherPriorityTaskWoken3 = pdFALSE;


    if (xSemaphoreTakeFromISR(HandleUDP, &xHigherPriorityTaskWoken1) ==
        pdTRUE) {

        char send = 0;
        if (strncmp(buffer, "INC", (read_size < 3) ? read_size : 3) ==
            0) {
            move = INC;
            send = 1;
        }
        else if (strncmp(buffer, "DEC",
                         (read_size < 3) ? read_size : 3) == 0) {
            move = DEC;
            send = 1;
        }
        else if (strncmp(buffer, "HALT",
                         (read_size < 4) ? read_size : 4) == 0) {
            move = HALT;
            send = 1;
            printf("HALT\n");
        }

        if (Movement && send) {
            xQueueSendFromISR(Movement, (void *)&move,
                              &xHigherPriorityTaskWoken2);
        }
        xSemaphoreGiveFromISR(HandleUDP, &xHigherPriorityTaskWoken3);

        portYIELD_FROM_ISR(xHigherPriorityTaskWoken1 |
                           xHigherPriorityTaskWoken2 |
                           xHigherPriorityTaskWoken3);
    }
    else {
        fprintf(stderr, "[ERROR] Overlapping UDPHandler call\n");
    }
}

void Control_Multiplayer(void *pvParameters)
{
    const char *attacking = "ATTACKING";
    const char *passive = "PASSIVE";
    const char *resume = "RESUME";
    const char *pause = "PAUSE";
    static char buffer[50];
    char *address = NULL;
    in_port_t port = UDP_TEST_PORT_1;
    signed int difference = 0;
    signed int last_difference = 0;
    signed int mothership_x = 0;
    signed int x_player = 0;
    bool active_bullet = false;
    bool active_bullet_previous = true;
    int difficulty = 1;
    int previous_difficulty = -1;
    bool pause_resumed = true;
    bool previous_pause_resumed = false;
    udp_soc_receive = aIOOpenUDPSocket(address, port, UDP_BUFFER_SIZE, UDPHandler, NULL);
    printf("UDP socket opened on port %d\n", port);
    vTaskSuspend(NULL);
    while (1) {

        while (xQueueReceive(Mothership_UDP, &mothership_x, 0) == pdTRUE)
        {}
        while (xQueueReceive(Bullet_active, &active_bullet, 0) == pdTRUE)
        {}
        while (xQueueReceive(Pause_Resumed, &pause_resumed, 0) == pdTRUE)
        {}
        while (xQueueReceive(Difficulty, &difficulty, 0) == pdTRUE)
        {}
        while (xQueueReceive(X_player, &x_player, 0) == pdTRUE)
        {}

        if (previous_pause_resumed != pause_resumed) {

            previous_pause_resumed = pause_resumed;
        }
        strcpy(buffer, pause_resumed ? resume : pause);

        aIOSocketPut(UDP, NULL, UDP_TEST_PORT_2, buffer, strlen(buffer));


        if (active_bullet_previous != active_bullet) {

            active_bullet_previous = active_bullet;
        }
        strcpy(buffer, active_bullet ? attacking : passive);

        aIOSocketPut(UDP, NULL, UDP_TEST_PORT_2, buffer, strlen(buffer));


        if (previous_difficulty != difficulty) {
            printf("Change\n");

            previous_difficulty = difficulty;
        }
        sprintf(buffer, "D%d", difficulty + 1);

        aIOSocketPut(UDP, NULL, UDP_TEST_PORT_2, buffer, strlen(buffer));

        difference = x_player - mothership_x;

        if (last_difference != difference) {

            last_difference = difference;
        }
        if (difference > 0) {
            sprintf(buffer, "+%d", difference);
            aIOSocketPut(UDP, NULL, UDP_TEST_PORT_2, buffer, strlen(buffer));
        }


        else {
            sprintf(buffer, "-%d", -difference);
            aIOSocketPut(UDP, NULL, UDP_TEST_PORT_2, buffer, strlen(buffer));

        }


        vTaskDelay(pdMS_TO_TICKS(15));
    }
}






void checkDraw(unsigned char status, const char *msg)
{
    if (status) {
        if (msg)
            fprints(stderr, "[ERROR] %s, %s\n", msg,
                    tumGetErrorMessage());
        else {
            fprints(stderr, "[ERROR] %s\n", tumGetErrorMessage());
        }
    }
}



void vSwapBuffers(void *pvParameters)
{
    TickType_t xLastWakeTime;
    xLastWakeTime = xTaskGetTickCount();
    const TickType_t frameratePeriod = 10;

    tumDrawBindThread(); // Setup Rendering handle with correct GL context

    while (1) {

        if (xSemaphoreTake(ScreenLock, portMAX_DELAY) == pdTRUE) {
            tumDrawUpdateScreen();
            tumEventFetchEvents(FETCH_EVENT_BLOCK);
            xSemaphoreGive(ScreenLock);
            xSemaphoreGive(DrawSignal);
            vTaskDelayUntil(&xLastWakeTime,
                            pdMS_TO_TICKS(frameratePeriod));
        }
    }
}

void xGetButtonInput(void)
{

    if (xSemaphoreTake(buttons.lock, 0) == pdTRUE) {
        xQueueReceive(buttonInputQueue, &buttons.buttons, 0);
        xSemaphoreGive(buttons.lock);
    }
}
void Show_next_level(void *pvParameters)
{

    int time_difference = 0;
    TickType_t xLastWakeTime = 0;
    TickType_t prevLastWakeTime = 0;
    // Initialise the xLastWakeTime variable with the current time.
    int start = 0;
    int pressed_replay = 0;
    int pressed_pause = 0;
    vTaskSuspend(NULL);
    bool pause_resume_for_control_multiplay = true;


    while (1) {


        if (!start)
        { prevLastWakeTime = xTaskGetTickCount();  }
        if (my_Substract) {
            vTaskSuspend(my_Substract);
        }
        if (move_player_right) {
            vTaskSuspend(move_player_right);
        }
        if (mothership) {
            vTaskSuspend(mothership);
        }
        if (mothership_on_off) {
            vTaskSuspend(mothership_on_off);
        }

        if (enemy_bullet) {
            vTaskSuspend(enemy_bullet);
        }
        if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {
            if (player1.dead_of_player == 1) {
                player1.break_show_text_dead_player = 1;
                printf("Show  text dead player is broken\n");
            }
        }
        xSemaphoreGive(player1.lock);
        if (mothership_multiplayer) {
            vTaskSuspend(mothership_multiplayer);
        }

        if (positions) {
            vTaskSuspend(positions);
        }
        if (help_to_positions_of_enemy) {
            vTaskSuspend(help_to_positions_of_enemy);
        }

        xLastWakeTime = xTaskGetTickCount();
        time_difference = xLastWakeTime - prevLastWakeTime;
        start++;

        //Break to set variable on the other way and reset time from this task

        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
            if (my_global_values.pressed_replay == 1 || my_global_values.pressed_pause == 1) {
                time_difference = 2000;

            }
        }
        xSemaphoreGive(my_global_values.lock);



        if (time_difference > 1000) {
            if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {

                if (my_global_values.pressed_replay == 1) {


                    my_global_values.give_new_replay = 1;
                    printf("Give bei Replay\n");


                }
                else if (my_global_values.pressed_pause == 1) {


                    printf("Give bei Pause\n");


                    my_global_values.give_new_values = 1;
                    pressed_pause = 1;






                }

                else {
                    /* code */
                    printf("Give alone\n");



                    my_global_values.level = my_global_values.level + 1;
                    my_global_values.right = 0;
                    my_global_values.left = 1000;
                    my_global_values.five = 10;
                    my_global_values.live = 3;
                    my_global_values.change_position = 0;
                    my_global_values.seconds = 0;
                    my_global_values.y = 0;
                    my_global_values.killed_enemies = 0;
                    my_global_values.speed = 400 - (my_global_values.level * 50);
                    my_global_values.game_over = 0;
                    my_global_values.pressed_replay = 0;



                    if (positions) {
                        vTaskResume(positions);
                    }
                    if (help_to_positions_of_enemy) {
                        vTaskResume(help_to_positions_of_enemy);
                    }
                    if (xSemaphoreTake(mothership_enemy.lock, 0) == pdTRUE) {
                        if (mothership_enemy.multiplay_game == true) {
                            vTaskResume(mothership_multiplayer);
                        }
                        else {
                            if (mothership_on_off) {
                                vTaskResume(mothership_on_off);
                            }
                        }
                    }
                    xSemaphoreGive(my_global_values.lock);


                    printf("NEXT LEVEL\n");


                }
            }
            xSemaphoreGive(my_global_values.lock);

            if (pressed_pause == 0) {


                if (xSemaphoreTake(mothership_enemy.lock, 0) == pdTRUE) {
                    mothership_enemy.mothership.x_pixel = -20;
                    mothership_enemy.mothership.y_pixel = 2;
                    mothership_enemy.mothership.dead = 0;

                }
                xSemaphoreGive(mothership_enemy.lock);
                if (xSemaphoreTake(enemies.lock, 0) == pdTRUE) {
                    for (int i = 0; i < 5; i++) {
                        for (int j = 0; j < 8; j++) {
                            enemies.enemy_position[i][j].dead = 0;
                            enemies.enemy_position[i][j].x_pixel = 0;
                            enemies.enemy_position[i][j].y_pixel = 0;
                        }

                    }
                }
                xSemaphoreGive(enemies.lock);
                if (xSemaphoreTake(green_blocks.lock, 0) == pdTRUE) {
                    for (int i = 0; i < 2; i++) {
                        for (int j = 0; j < 20; j++) {
                            green_blocks.blocks_blocks[i][j].block_off = 0;
                        }
                    }
                }
                xSemaphoreGive(green_blocks.lock);
                if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {
                    bullet_of_enemy.bullet_on = 0;
                    bullet_of_enemy.position_take = 0;

                }
                xSemaphoreGive(bullet_of_enemy.lock);

                if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {
                    bullet_of_player.dead_player = 0;
                    bullet_of_player.bullet_on = 0;
                    bullet_of_player.x_pixel_of_bullet = SCREEN_WIDTH / 2 + 10;
                    bullet_of_player.y_pixel_of_bullet = SCREEN_HEIGHT - 50;
                    bullet_of_player.position_take = 0;
                }
                xSemaphoreGive(bullet_of_player.lock);



                if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {
                    player1.dead_of_player = 0;
                    player1.position_take = 0;
                    player1.x_pixel_of_player = SCREEN_WIDTH / 2;
                    player1.y_pixel_of_player = SCREEN_HEIGHT - 50;
                    player1.position_take = 0;
                }
                xSemaphoreGive(player1.lock);

            }

            pressed_pause = 0;

            time_difference = 0;
            start = 0;

            vTaskSuspend(NULL);

        }

    }
}


void Show_text_dead_player(void *pvParameters)
{



    int time_difference = 0;
    TickType_t xLastWakeTime = 0;
    TickType_t prevLastWakeTime = 0;
    // Initialise the xLastWakeTime variable with the current time.
    int start = 0;
    vTaskSuspend(NULL);

    while (1) {

        if (!start) {
            if (my_Substract) {
                vTaskSuspend(my_Substract);
            }
            if (move_player_right) {
                vTaskSuspend(move_player_right);
            }
            prevLastWakeTime = xTaskGetTickCount();
        }

        xLastWakeTime = xTaskGetTickCount();
        time_difference = xLastWakeTime - prevLastWakeTime;
        start++;

        //Break if to set values on the other way

        if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {
            if (player1.break_show_text_dead_player == 1) {
                time_difference = 1000;
                player1.break_show_text_dead_player = 0;
            }
        }
        xSemaphoreGive(player1.lock);



        if (time_difference > 500) {
            if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {
                bullet_of_player.dead_player = 0;
                bullet_of_player.bullet_on = 0;
            }
            xSemaphoreGive(bullet_of_player.lock);

            if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                my_global_values.live = my_global_values.live - 1;
                if (my_global_values.live == 0) {
                    my_global_values.game_over = 1;
                }
            }
            xSemaphoreGive(bullet_of_player.lock);

            if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {
                player1.dead_of_player = 0;
            }
            xSemaphoreGive(player1.lock);
            printf("Broken\n");

            start = 0;
            vTaskSuspend(NULL);

        }
        vTaskDelay(1);

    }
}

void Mothership_on_off(void *pvParameters)
{
    TickType_t xLastWakeTime;
    const TickType_t xFrequency = 5000 / portTICK_PERIOD_MS;
    // Initialise the xLastWakeTime variable with the current time.
    xLastWakeTime = xTaskGetTickCount();
    vTaskSuspend(NULL);

    while (1) {
        printf("MOTHERSHIP\n");
        xLastWakeTime = xTaskGetTickCount();
        vTaskResume(mothership);
        vTaskDelayUntil(&xLastWakeTime, xFrequency);


    }

}

void Mothership_multiplayer(void *pvParameters)
{
    TickType_t xLastWakeTime;
    const TickType_t xFrequency = 10 / portTICK_PERIOD_MS;
    signed int x_pixel = 20;
    signed int x_pixel_previous = 20;
    int y_pixel = 2;
    bool inc = false;
    bool halt = false;
    bool dec = false;
    static opponent_cmd_t current_key = HALT;
    int recognised = 0;

    // Initialise the xLastWakeTime variable with the current time.
    xLastWakeTime = xTaskGetTickCount();
    if (xSemaphoreTake(mothership_enemy.lock, 0) == pdTRUE) {
        mothership_enemy.mothership.x_pixel = -20;
        mothership_enemy.mothership.y_pixel = 2;

    }
    xSemaphoreGive(mothership_enemy.lock);
    vTaskSuspend(NULL);
    while (1)  {




        if (xSemaphoreTake(mothership_enemy.lock, 0) == pdTRUE) {


            if (mothership_enemy.mothership.x_pixel < SCREEN_WIDTH / 2 + 100 && mothership_enemy.collision_happend == 0 && mothership_enemy.mothership.x_pixel > 0) {
                if (Movement)
                { xQueueReceive(Movement, &current_key, 0); }

                if (current_key == INC) {
                    mothership_enemy.mothership.x_pixel = mothership_enemy.mothership.x_pixel + 1;
                    x_pixel_previous = mothership_enemy.mothership.x_pixel;


                }
                if (current_key == DEC) {
                    mothership_enemy.mothership.x_pixel = mothership_enemy.mothership.x_pixel - 1;
                    x_pixel_previous = mothership_enemy.mothership.x_pixel;
                }

                if (current_key == HALT) {
                    recognised++;
                }
                if (recognised > 0) {
                    printf("RECOGNISED\n");
                    recognised = 0;

                }

            }


            else {
                mothership_enemy.mothership.x_pixel = SCREEN_WIDTH / 2;
                mothership_enemy.mothership.dead = 0;
                mothership_enemy.collision_happend = 0;


            }
        }
        xSemaphoreGive(mothership_enemy.lock);

        vTaskDelay(10);
    }

}
void Mothership(void *pvParameters)
{
    TickType_t xLastWakeTime;
    const TickType_t xFrequency = 10 / portTICK_PERIOD_MS;
    // Initialise the xLastWakeTime variable with the current time.
    xLastWakeTime = xTaskGetTickCount();
    if (xSemaphoreTake(mothership_enemy.lock, 0) == pdTRUE) {
        mothership_enemy.mothership.x_pixel = -20;
        mothership_enemy.mothership.y_pixel = 2;


    }
    xSemaphoreGive(mothership_enemy.lock);

    vTaskSuspend(NULL);

    while (1) {


        xLastWakeTime = xTaskGetTickCount();
        if (xSemaphoreTake(mothership_enemy.lock, 0) == pdTRUE) {
            mothership_enemy.mothership.dead = 0;
            if (mothership_enemy.mothership.x_pixel < SCREEN_WIDTH / 2 + 100 && mothership_enemy.collision_happend == 0) {
                mothership_enemy.mothership.x_pixel = mothership_enemy.mothership.x_pixel + 1;
            }
            else {
                mothership_enemy.mothership.x_pixel = -20;
                mothership_enemy.mothership.dead = 0;
                mothership_enemy.collision_happend = 0;
                xSemaphoreGive(mothership_enemy.lock);
                vTaskSuspend(NULL);
            }

        }
        xSemaphoreGive(mothership_enemy.lock);
        vTaskDelayUntil(&xLastWakeTime, xFrequency);
    }

}
void Positions(void *pvParameters)
{


    int x_coord_origin = 0;
    int y_coord_origin = 0;
    int temporary_x;
    int temporary_y = 0;
    int previous_temporary_y = 1000;
    int bullet_x_pixel;
    int bullet_y_pixel;

    bullet_player_t bullet_collision = { 0 };
    bullet_player_t bullet_of_enemy_collision = {0};
    bullet_player_t bullet_collision_for_mother = {100};

    enemies_position_t enemies_collision[5][8] = { 0 };
    int distance_collision_x = 100;
    int distance_collision_y = 100;
    int distance_collision_bullet_pl_block_x = 100;
    int distance_collision_bullet_pl_block_y = 100;
    int distance_collision_bullet_enemy_block_x = 100;
    int distance_collision_bullet_enemy_block_y = 100;
    blocks_position_t blocks_save_local[2][20] = {0};
    int distance_collision_bullets_x = 100;
    int distance_collision_bullets_y = 100;
    int distance_collision_mother_x = 100;
    int distance_collision_mother_y = 100;
    int distance_collision_bullet_enemy_and_player_x = 100;
    int distance_colision_bullet_enemy_and_player_y = 100;
    int killed_enemies = 0;
    int game_over = 0;
    int do_not_use_buttons_press = 0;


    enemies_position_t mum = { 0 };




    if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {
        player1.x_pixel_of_player = SCREEN_WIDTH / 2;
        player1.y_pixel_of_player = SCREEN_HEIGHT - 50;

    }
    xSemaphoreGive(player1.lock);

    int add_to_block_x_pixel = 70;
    int add_to_block_y_pixel = SCREEN_HEIGHT - 50;



    int substact = 0;
    int bullet_on_off = 0;
    int times_pressed_w = 0;


    int add_to_x_pixel = 0;
    int add_to_y_pixel = 0;

    int right = 0;
    int left = 1000;
    int m = 0;
    int size_of_array_for_bullet_of_enemy = 0;
    int random_number = 0;
    int player_dead = 0;
    int x_player = 0;
    int y_player = 0;
    int score = 0;
    int x_player_bullet_on = 0;
    bool allow_draw = false;

    printf("POSITIONS\n");
    vTaskSuspend(NULL);

    while (1) {

        if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {
            x_player_bullet_on = bullet_of_player.bullet_on;
        }
        xSemaphoreGive(bullet_of_player.lock);



        if (xSemaphoreTake(mothership_enemy.lock, 0) == pdTRUE) {
            mum.x_pixel = mothership_enemy.mothership.x_pixel;
            mum.y_pixel = mothership_enemy.mothership.y_pixel;
            mum.dead = mothership_enemy.mothership.dead;

        }
        xSemaphoreGive(mothership_enemy.lock);

        if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {
            x_player = player1.x_pixel_of_player;
            y_player = player1.y_pixel_of_player;


        }
        xSemaphoreGive(player1.lock);

        //VALUES FROM HELP TO POSITION

        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
            temporary_x = my_global_values.seconds;
            temporary_y = my_global_values.y;

        }
        xSemaphoreGive(my_global_values.lock);


        //TAKE RIGHT AND LEFT MAX PIXEL FROM LIFE ENEMY AND GIVE TO HELP TO POSITIONS

        if (xSemaphoreTake(enemies.lock, 0) == pdTRUE) {
            right = 0;
            left = 1000;
            for (int i = 0; i < 5; i++) {
                x_coord_origin = 50;
                y_coord_origin = y_coord_origin + 50;

                for (int j = 0; j < 8; j++) {
                    enemies.enemy_position[i][j].x_pixel = x_coord_origin + temporary_x;
                    enemies.enemy_position[i][j].y_pixel = y_coord_origin + temporary_y;



                    if (enemies.enemy_position[i][j].x_pixel < left && !enemies.enemy_position[i][j].dead) {
                        left = enemies.enemy_position[i][j].x_pixel;

                    }
                    if (enemies.enemy_position[i][j].x_pixel > right && !enemies.enemy_position[i][j].dead) {
                        right = enemies.enemy_position[i][j].x_pixel;

                    }

                    x_coord_origin = x_coord_origin + 40;

                }

            }
        }
        xSemaphoreGive(enemies.lock);

        y_coord_origin = 0;



        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
            my_global_values.right = right;
            my_global_values.left = left;


        }
        xSemaphoreGive(my_global_values.lock);

        if (do_not_use_buttons_press == 1 || x_player_bullet_on == 1) {

            substact = 0;
            add_to_x_pixel = 0;
            times_pressed_w = 0;
            bullet_on_off = 0;
            do_not_use_buttons_press = 0;
            x_player_bullet_on = 0;
        }




        if (xSemaphoreTake(buttons.lock, 0) == pdTRUE) {
            if (buttons.buttons[KEYCODE(D)]) {
                add_to_x_pixel++;
            }
            if (add_to_x_pixel > 0) {
                if (!buttons.buttons[KEYCODE(D)]) {
                    add_to_x_pixel = 0;
                }
            }

            if (buttons.buttons[KEYCODE(A)]) {
                substact++;
            }
            if (substact > 0) {
                if (!buttons.buttons[KEYCODE(A)]) {
                    substact = 0;
                }
            }
            if (x_player_bullet_on == 0) {

                if (buttons.buttons[KEYCODE(W)]) {
                    bullet_on_off++;

                }
                if (bullet_on_off > 0) {
                    if (!buttons.buttons[KEYCODE(W)]) {
                        printf("W pressed\n");
                        times_pressed_w++;
                        bullet_on_off = 0;
                    }
                }
            }
        }
        xSemaphoreGive(buttons.lock);

        if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {
            player_dead = bullet_of_player.dead_player;


            if (!bullet_of_player.dead_player)

            {
                if (add_to_x_pixel > 0) {
                    vTaskResume(move_player_right);
                }
                else {
                    vTaskSuspend(move_player_right);
                }
                if (substact > 0) {
                    vTaskResume(my_Substract);
                }
                else {
                    vTaskSuspend(my_Substract);
                }

            }
            else {
                add_to_x_pixel = 0;
                substact = 0;
                bullet_on_off = 0;
                times_pressed_w = 0;
            }

            if (bullet_of_player.bullet_on == 0 && bullet_of_player.dead_player == 0 && times_pressed_w > 0) {
                times_pressed_w = 0;


                if (bullet_of_player_task)
                { vTaskResume(bullet_of_player_task);}



            }
        }
        xSemaphoreGive(bullet_of_player.lock);

        //Constructe green blocks


        if (xSemaphoreTake(green_blocks.lock, 0) == pdTRUE) {

            for (int i = 0; i < 2; i++) {
                add_to_block_x_pixel = 70;
                int counter = 0;
                for (int j = 0; j < 20; j++) {
                    add_to_block_x_pixel = add_to_block_x_pixel + 10;



                    if (j % 5 == 0 && j != 0) {

                        add_to_block_x_pixel = add_to_block_x_pixel + 50;
                        green_blocks.blocks_blocks[i][j].x_pixel_of_block = add_to_block_x_pixel;
                        blocks_save_local[i][j].x_pixel_of_block = green_blocks.blocks_blocks[i][j].x_pixel_of_block;
                        blocks_save_local[i][j].block_off = green_blocks.blocks_blocks[i][j].block_off;


                    }
                    else {
                        green_blocks.blocks_blocks[i][j].x_pixel_of_block = add_to_block_x_pixel;
                        blocks_save_local[i][j].x_pixel_of_block = green_blocks.blocks_blocks[i][j].x_pixel_of_block;
                        blocks_save_local[i][j].block_off = green_blocks.blocks_blocks[i][j].block_off;
                    }

                    if (i == 0) {
                        green_blocks.blocks_blocks[i][j].y_pixel_of_block = add_to_block_y_pixel;
                        blocks_save_local[i][j].y_pixel_of_block = green_blocks.blocks_blocks[i][j].y_pixel_of_block;
                        blocks_save_local[i][j].block_off = green_blocks.blocks_blocks[i][j].block_off;
                    }
                    if (i == 1) {
                        green_blocks.blocks_blocks[i][j].y_pixel_of_block = add_to_block_y_pixel + 10;
                        blocks_save_local[i][j].y_pixel_of_block = green_blocks.blocks_blocks[i][j].y_pixel_of_block;
                        blocks_save_local[i][j].block_off = green_blocks.blocks_blocks[i][j].block_off;
                    }

                }
            }

        }
        xSemaphoreGive(green_blocks.lock);


        add_to_block_x_pixel = 50;
        add_to_block_y_pixel = SCREEN_HEIGHT - 100;






        if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {
            if (bullet_of_player.bullet_on) {
                bullet_collision.x_pixel_of_bullet = bullet_of_player.x_pixel_of_bullet;
                bullet_collision.y_pixel_of_bullet = bullet_of_player.y_pixel_of_bullet;
                bullet_collision.bullet_on = bullet_of_player.bullet_on;
                bullet_collision_for_mother.x_pixel_of_bullet = bullet_of_player.x_pixel_of_bullet;
                bullet_collision_for_mother.y_pixel_of_bullet = bullet_of_player.y_pixel_of_bullet;
                bullet_collision_for_mother.bullet_on = bullet_of_player.bullet_on;
            }

        }
        xSemaphoreGive(bullet_of_player.lock);
        if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {

            bullet_of_enemy_collision.x_pixel_of_bullet = bullet_of_enemy.x_pixel_of_bullet;
            bullet_of_enemy_collision.y_pixel_of_bullet = bullet_of_enemy.y_pixel_of_bullet;
            bullet_of_enemy_collision.bullet_on = bullet_of_enemy.bullet_on;

        }
        xSemaphoreGive(bullet_of_enemy.lock);

        //Take enemy positions for collision

        if (xSemaphoreTake(enemies.lock, 0) == pdTRUE) {
            for (int i = 0; i < 5; i++) {
                for (int j = 0; j < 8; j++) {
                    enemies_collision[i][j].x_pixel = enemies.enemy_position[i][j].x_pixel;
                    enemies_collision[i][j].y_pixel = enemies.enemy_position[i][j].y_pixel;
                    enemies_collision[i][j].dead = enemies.enemy_position[i][j].dead;
                    if (!enemies_collision[i][j].dead && enemies_collision[i][j].y_pixel + 18 > SCREEN_HEIGHT - 110) {
                        game_over = 1;
                    }

                }
            }
        }
        xSemaphoreGive(enemies.lock);


        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
            if (game_over) {
                my_global_values.game_over = game_over;
                game_over = 0;
            }
        }
        xSemaphoreGive(my_global_values.lock);

        //Size for array where enemies are alive

        for (int i = 7; i > -1; i--) {

            for (int j = 4; j > -1; j--) {
                if (!enemies_collision[j][i].dead) {
                    size_of_array_for_bullet_of_enemy++;
                    break;
                }
            }
        }


        //Save alive in one separate array, choose random element and give coordinates to him

        if (size_of_array_for_bullet_of_enemy > 0) {


            enemies_position_t enemy_to_shoot[size_of_array_for_bullet_of_enemy];
            m = 0;
            for (int i = 7; i > -1; i--) {

                if (m >= size_of_array_for_bullet_of_enemy) {

                    break;
                }
                for (int j = 4; j > -1; j--) {
                    if (!enemies_collision[j][i].dead)

                    {
                        enemy_to_shoot[m].x_pixel = enemies_collision[j][i].x_pixel;
                        enemy_to_shoot[m].y_pixel = enemies_collision[j][i].y_pixel;
                        enemy_to_shoot[m].dead = enemies_collision[j][i].dead;
                        m++;
                        break;
                    }
                }
            }
            srand(time(NULL));
            random_number = rand() % size_of_array_for_bullet_of_enemy;





            if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {
                if (!bullet_of_enemy.bullet_on) {


                    bullet_of_enemy.x_pixel_of_bullet = enemy_to_shoot[random_number].x_pixel;
                    bullet_of_enemy.y_pixel_of_bullet = enemy_to_shoot[random_number].y_pixel;


                    xSemaphoreGive(bullet_of_enemy.lock);
                    if (enemy_bullet) {
                        vTaskResume(enemy_bullet);
                    }
                }
                else {
                    xSemaphoreGive(bullet_of_enemy.lock);
                }
            }


            size_of_array_for_bullet_of_enemy = 0;

        }



        //COLLISION PLAYER'S BULLET ENEMY



        if (bullet_collision.bullet_on) {

            for (int i = 0; i < 5; i++) {
                for (int j = 0; j < 8; j++) {
                    if (enemies_collision[i][j].dead) {
                        continue;
                    }
                    distance_collision_x = enemies_collision[i][j].x_pixel - bullet_collision.x_pixel_of_bullet;
                    distance_collision_y = enemies_collision[i][j].y_pixel - bullet_collision.y_pixel_of_bullet;
                    if (distance_collision_x < 2 && distance_collision_x > -18)
                        if (distance_collision_y > -18 && distance_collision_y < 10) {

                            printf("Collision happend,between enemy and player's bullet\n");

                            if (xSemaphoreTake(enemies.lock, 0) == pdTRUE) {
                                enemies.enemy_position[i][j].dead = 1;


                            }
                            xSemaphoreGive(enemies.lock);

                            distance_collision_y = 100;
                            distance_collision_x = 100;

                            if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {
                                bullet_of_player.collision_happend = 1;

                            }
                            xSemaphoreGive(bullet_of_player.lock);

                            if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {




                                my_global_values.speed = my_global_values.speed - 4;
                                my_global_values.killed_enemies = my_global_values.killed_enemies + 1;
                                if (my_global_values.killed_enemies == 40) {
                                    do_not_use_buttons_press = 1;
                                    if (show_next_level) {
                                        vTaskResume(show_next_level);
                                    }

                                }



                                printf("Killed enemies: %d\n", my_global_values.killed_enemies);

                                if (i == 0) {
                                    my_global_values.score = my_global_values.score + 30;
                                }
                                if (i == 1 || i == 2) {
                                    my_global_values.score = my_global_values.score + 20;
                                }
                                if (i == 3 || i == 4) {
                                    my_global_values.score = my_global_values.score + 10;
                                }


                            }
                            xSemaphoreGive(my_global_values.lock);


                        }
                }
            }
        }

        //COLLISION BLOCK ENEMY'S BULLET

        if (bullet_of_enemy_collision.bullet_on) {


            for (int i = 0; i < 2; i++) {
                for (int j = 0; j < 20; j++) {
                    if (blocks_save_local[i][j].block_off) {
                        continue;
                    }
                    distance_collision_bullet_enemy_block_x = blocks_save_local[i][j].x_pixel_of_block - bullet_of_enemy_collision.x_pixel_of_bullet - 10;
                    distance_collision_bullet_enemy_block_y = blocks_save_local[i][j].y_pixel_of_block - bullet_of_enemy_collision.y_pixel_of_bullet - 10;
                    if (distance_collision_bullet_enemy_block_x < 2 && distance_collision_bullet_enemy_block_x > -10)
                        if (distance_collision_bullet_enemy_block_y > -5 && distance_collision_bullet_enemy_block_y < 10) {
                            printf("Collision block enemy bullet happend\n");



                            if (xSemaphoreTake(green_blocks.lock, 0) == pdTRUE) {
                                green_blocks.blocks_blocks[i][j].block_off = 1;
                            }
                            xSemaphoreGive(green_blocks.lock);
                            distance_collision_bullet_enemy_block_x = 100;
                            distance_collision_bullet_enemy_block_y = 100;

                            if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {

                                bullet_of_enemy.collision_happend = 1;

                            }
                            xSemaphoreGive(bullet_of_enemy.lock);




                        }

                }
            }

        }
        //COLLISION PLAYER'S BULLET BLOCK
        if (bullet_collision.bullet_on) {


            for (int i = 0; i < 2; i++) {
                for (int j = 0; j < 20; j++) {
                    if (blocks_save_local[i][j].block_off) {
                        continue;
                    }

                    distance_collision_bullet_pl_block_x = blocks_save_local[i][j].x_pixel_of_block - bullet_collision.x_pixel_of_bullet;
                    distance_collision_bullet_pl_block_y = blocks_save_local[i][j].y_pixel_of_block - bullet_collision.y_pixel_of_bullet;
                    if (distance_collision_bullet_pl_block_x < 2 && distance_collision_bullet_pl_block_x > -10)
                        if (distance_collision_bullet_pl_block_y > -10 && distance_collision_bullet_pl_block_y < 10) {
                            printf("Collision bullet player block\n");

                            if (xSemaphoreTake(green_blocks.lock, 0) == pdTRUE) {
                                green_blocks.blocks_blocks[i][j].block_off = 1;
                            }
                            xSemaphoreGive(green_blocks.lock);

                            distance_collision_bullet_pl_block_x = 100;
                            distance_collision_bullet_pl_block_y = 100;

                            if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {
                                bullet_of_player.collision_happend = 1;
                                printf("Value block, bullet of player changed\n");

                            }
                            xSemaphoreGive(bullet_of_player.lock);






                        }

                }
            }
        }

        //COLLISION MOTHER AND PLAYER'S BULLET
        if (bullet_collision_for_mother.bullet_on) {

            if (!mum.dead) {

                distance_collision_mother_x = mum.x_pixel - bullet_collision_for_mother.x_pixel_of_bullet;
                distance_collision_mother_y = mum.y_pixel - bullet_collision_for_mother.y_pixel_of_bullet;

                if (distance_collision_mother_x < 2 && distance_collision_mother_x > -20) {
                    if (distance_collision_mother_y < 10 && distance_collision_mother_y > -20) {

                        if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {
                            bullet_of_player.collision_happend = 1;
                        }
                        xSemaphoreGive(bullet_of_player.lock);

                        if (xSemaphoreTake(mothership_enemy.lock, 0) == pdTRUE) {
                            mothership_enemy.collision_happend = 1;
                        }
                        xSemaphoreGive(mothership_enemy.lock);

                        printf("Distance collision X: %d\n", distance_collision_mother_x);
                        printf("Distance collision Y: %d\n", distance_collision_mother_y);
                        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                            my_global_values.score = my_global_values.score + 50;
                        }
                        xSemaphoreGive(my_global_values.lock);

                        distance_collision_mother_x = 100;
                        distance_collision_mother_y = 100;

                        printf("COLLISION\n");

                    }

                }
            }
        }

        //COLLISION ENEMY'S BULLET PLAYER

        if (player_dead == 0 && bullet_of_enemy_collision.bullet_on) {
            distance_collision_bullet_enemy_and_player_x = x_player - (bullet_of_enemy_collision.x_pixel_of_bullet + 10);
            distance_colision_bullet_enemy_and_player_y = y_player - (bullet_of_enemy_collision.y_pixel_of_bullet + 10);


            if (distance_collision_bullet_enemy_and_player_x < 2 && distance_collision_bullet_enemy_and_player_x > -18) {
                if (distance_colision_bullet_enemy_and_player_y > -18 && distance_colision_bullet_enemy_and_player_y < 10)

                {

                    player_dead = 1;

                    if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {

                        bullet_of_player.dead_player = 1;

                    }
                    xSemaphoreGive(bullet_of_player.lock);



                    if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {
                        player1.dead_of_player = 1;

                    }
                    xSemaphoreGive(player1.lock);

                    distance_colision_bullet_enemy_and_player_y = 100;
                    distance_collision_bullet_enemy_and_player_x = 100;

                    if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {
                        bullet_of_enemy.collision_happend = 1;

                    }
                    xSemaphoreGive(bullet_of_enemy.lock);

                    if (show_text_dead_player) {
                        do_not_use_buttons_press = 1;
                        vTaskResume(show_text_dead_player);
                    }


                }
            }
        }


        //COLLISION BULLET'S


        if (bullet_collision.bullet_on && bullet_of_enemy_collision.bullet_on)

        {
            distance_collision_bullets_x = (bullet_of_enemy_collision.x_pixel_of_bullet + 10) - bullet_collision.x_pixel_of_bullet;
            distance_collision_bullets_y = (bullet_of_enemy_collision.y_pixel_of_bullet + 10) - bullet_collision.y_pixel_of_bullet;

            if (distance_collision_bullets_x > -4 && distance_collision_bullets_x < 4) {
                if (distance_collision_bullets_y < 10 && distance_collision_bullets_y > -10) {
                    if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {
                        bullet_of_enemy.collision_happend = 1;
                    }
                    xSemaphoreGive(bullet_of_enemy.lock);


                    if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {
                        bullet_of_player.collision_happend = 1;
                    }
                    xSemaphoreGive(bullet_of_player.lock);

                    distance_collision_bullets_y = 100;
                    distance_collision_bullets_x = 100;
                }

            }
        }
        //   RESET_VALUES


        bullet_collision.x_pixel_of_bullet = 2000;
        bullet_collision.y_pixel_of_bullet = 2000;
        bullet_of_enemy_collision.x_pixel_of_bullet = 3000;
        bullet_of_enemy_collision.y_pixel_of_bullet = 3000;
        bullet_collision_for_mother.x_pixel_of_bullet = 100;
        bullet_collision_for_mother.y_pixel_of_bullet = 100;
        x_player = 1000;
        y_player = 1000;




        //free "old" values

        vTaskDelay(3);
    }
}

//Here are all functions which are required for exercise 3



void Help_to_positions_of_enemy(void *pvParameters)
{
    TickType_t xLastWakeTime;
    TickType_t xFrequency;
    // Initialise the xLastWakeTime variable with the current time.
    xLastWakeTime = xTaskGetTickCount();

    int previous_y = 2000;
    if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
        my_global_values.right = 0;
        my_global_values.left = 1000;
        my_global_values.five = 10;
        my_global_values.live = 3;
        my_global_values.speed = 400;
        xFrequency = my_global_values.speed / portTICK_PERIOD_MS;

    }
    xSemaphoreGive(my_global_values.lock);

    printf("Help to position of enemy\n");


    vTaskSuspend(NULL);
    while (1) {
        xLastWakeTime = xTaskGetTickCount();


        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
            xFrequency = my_global_values.speed;
            if (my_global_values.killed_enemies == 39) {
                xFrequency = 8;
            }



        }
        xSemaphoreGive(my_global_values.lock);

        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {

            if (my_global_values.change_position == 0) {
                my_global_values.change_position++;

                if (my_global_values.right > 430 || my_global_values.left < 50) {
                    my_global_values.y = my_global_values.y + 15;
                    my_global_values.five = -1 * my_global_values.five;

                    if (my_global_values.y == previous_y) {
                        printf("MISTAKE IN HELP TO POSITION\n");
                        vTaskSuspendAll();
                    }

                }
                my_global_values.seconds = my_global_values.seconds + my_global_values.five;

                previous_y = my_global_values.y;

            }
            else {
                my_global_values.change_position--;
            }

        }
        xSemaphoreGive(my_global_values.lock);
        vTaskDelayUntil(&xLastWakeTime, xFrequency);
    }
}
void Enemy_bullet(void *pvParameters)
{
    TickType_t xLastWakeTime;
    const TickType_t xFrequency = 5 / portTICK_PERIOD_MS;
    // Initialise the xLastWakeTime variable with the current time.
    xLastWakeTime = xTaskGetTickCount();

    int position_taken = 0;
    int x_pixel = 0;
    vTaskSuspend(NULL);



    while (1) {


        xLastWakeTime = xTaskGetTickCount();


        if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {
            if (bullet_of_enemy.position_take == 0) {
                position_taken = 1;
                x_pixel = bullet_of_enemy.x_pixel_of_bullet;

            }

        }
        xSemaphoreGive(bullet_of_enemy.lock);

        if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {
            bullet_of_enemy.bullet_on = 1;
            bullet_of_enemy.x_pixel_of_bullet = x_pixel;
            bullet_of_enemy.y_pixel_of_bullet = bullet_of_enemy.y_pixel_of_bullet + 1;


            if (bullet_of_enemy.y_pixel_of_bullet >= (SCREEN_HEIGHT - 43) || bullet_of_enemy.collision_happend) {
                position_taken = 0;
                bullet_of_enemy.bullet_on = 0;
                bullet_of_enemy.collision_happend = 0;
                x_pixel = 0;
                printf("Bullet  ENEMY off\n");

                xSemaphoreGive(bullet_of_enemy.lock);
                vTaskSuspend(NULL);


            }

        }
        xSemaphoreGive(bullet_of_enemy.lock);

        if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {
            bullet_of_enemy.position_take = position_taken;
        }
        xSemaphoreGive(bullet_of_enemy.lock);


        vTaskDelayUntil(&xLastWakeTime, xFrequency);

    }

}


void Bullet_of_player(void *pyParameters)
{
    TickType_t xLastWakeTime;
    bool bullet_on_of = false;
    const TickType_t xFrequency = 1 / portTICK_PERIOD_MS;
    // Initialise the xLastWakeTime variable with the current time.
    xLastWakeTime = xTaskGetTickCount();
    int counter = 0;
    int position_taken = 0;
    int x_pixel;
    if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {

        bullet_of_player.y_pixel_of_bullet = SCREEN_HEIGHT - 10;
    }
    xSemaphoreGive(bullet_of_player.lock);


    vTaskSuspend(NULL);

    while (1) {

        xLastWakeTime = xTaskGetTickCount();


        if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {

            if (player1.position_take == 0) {
                x_pixel = player1.x_pixel_of_player + 10;
                position_taken = 1;
            }
        }
        xSemaphoreGive(player1.lock);


        if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {
            bullet_of_player.bullet_on = 1;

            bullet_of_player.x_pixel_of_bullet = x_pixel;

            bullet_of_player.y_pixel_of_bullet = bullet_of_player.y_pixel_of_bullet - 1;
            if (bullet_of_player.y_pixel_of_bullet < 0 || bullet_of_player.collision_happend) {

                position_taken = 0;
                bullet_of_player.bullet_on = 0;



                bullet_of_player.y_pixel_of_bullet = SCREEN_HEIGHT - 10;
                bullet_of_player.collision_happend = 0;


                xSemaphoreGive(bullet_of_player.lock);
                vTaskSuspend(NULL);

            }
        }
        xSemaphoreGive(bullet_of_player.lock);
        if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {

            player1.position_take = position_taken;
        }
        xSemaphoreGive(player1.lock);


        vTaskDelayUntil(&xLastWakeTime, xFrequency);

    }
}

void My_Substract(void *pvParameters)
{
    TickType_t xLastWakeTime;
    const TickType_t xFrequency = 6 / portTICK_PERIOD_MS;


    // Initialise the xLastWakeTime variable with the current time.
    xLastWakeTime = xTaskGetTickCount();

    vTaskSuspend(NULL);

    while (1) {
        xLastWakeTime = xTaskGetTickCount();

        if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {

            if (player1.x_pixel_of_player > 70)
            {  player1.x_pixel_of_player = player1.x_pixel_of_player - 1;}
            else {
                xSemaphoreGive(player1.lock);
                vTaskSuspend(NULL);
            }

        }
        xSemaphoreGive(player1.lock);
        vTaskDelayUntil(&xLastWakeTime, xFrequency);
    }
}

void Move_player_right(void *pvParameters)
{
    TickType_t xLastWakeTime;
    const TickType_t xFrequency = 6 / portTICK_PERIOD_MS;

    // Initialise the xLastWakeTime variable with the current time.
    xLastWakeTime = xTaskGetTickCount();

    vTaskSuspend(NULL);

    while (1) {
        xLastWakeTime = xTaskGetTickCount();

        if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {
            if (player1.x_pixel_of_player < SCREEN_WIDTH - 200)
            { player1.x_pixel_of_player = player1.x_pixel_of_player + 1;}
            else {
                xSemaphoreGive(player1.lock);
                vTaskSuspend(NULL);
            }

        }
        xSemaphoreGive(player1.lock);
        vTaskDelayUntil(&xLastWakeTime, xFrequency);
    }
}

void Draw_everything(void *pvParameters)
{
    int counter = 0;
    int time_difference = 4000;
    TickType_t xLastWakeTime = 0;
    TickType_t prevLastWakeTime = 0;
    bool left_mouse = false;
    int difficulty = 1;
    int previous_difficulty = -1;


    signed int difference_between_x_pixels = 0;
    signed int difference_between_x_pixel_before = 0;
    bool pause_resumed_for_udp = true;
    bool bullet_on_off = false;
    bool bullet_on_off_previous = true;
    int x_player_previous;
    bool previous_pause_resumed_for_udp = false;
    signed int mum_x_pixel_previous = 0;




    enemies_position_t draw_x[5][8];
    int x_player;
    int y_player;
    int x_bullet_player;
    int y_bullet_player;
    blocks_position_t save_blocks_positions[2][20];
    int x_bullet_enemy;
    int y_bullet_enemy;
    enemies_position_t mum;

    int lives;
    int x_position_lives;
    int y_position_lives;
    int level = 0;
    int score = 0;
    int highscore;
    int high_score_multiplayer;
    int player_dead = 0;
    int killed_enemies = 0;
    static char str1[100] = {0};
    static char str2[200] = {0};
    static char str3[200] = {0};
    static char str4[200] = {0};
    static char str5[200] = {0};
    static char str6[300] = {0};
    static char str7[200] = {0};
    static char str8[200] = {0};
    static char str9[200] = {0};
    static char str10[200] = {0};
    static char str11[100] = {0};
    static char str12[100] = {0};
    static char str13[100] = {0};
    static char str14[100] = {0};
    static char str15[100] = {0};
    static char str16[100] = {0};
    static char str17[100] = {0};
    static char str18[100] = {0};
    static char str19[100] = {0};
    static char str20[100] = {0};
    static char str21[100] = {0};
    static char str22[100] = {0};
    static char str23[100] = {0};
    static char str24[100] = {0};


    int pause_resume = 0;

    int time_pressed_pause = 0;
    int start_game = 0;
    int replay = 0;
    int game_over = 0;
    int zero = 0;
    int zero_pressed = 0;
    int one = 0;
    int one_pressed = 0;
    int two = 0;
    int two_pressed = 0;
    int three = 0;
    int three_pressed = 0;
    int four = 0;
    int four_pressed = 0;
    int five = 0;
    int five_pressed = 0;
    int six = 0;
    int six_pressed = 0;
    int seven = 0;
    int seven_pressed = 0;
    int eight = 0;
    int eight_pressed = 0;
    int nine = 0;
    int nine_pressed = 0;

    int one_number_pressed = 0;

    int pause_pressed = 0;

    int go_back = 0;
    int increase_live = 0;
    int increase_live_pressed = 0;
    int see_high_level = 0;
    int see_high_level_pressed = 0;
    int set_starting_score = 0;
    int set_starting_score_pressed = 0;
    int array_for_set_starting_score[100] = {0};

    int clear = 0;
    int clear_pressed = 0;
    int start_game_multiplayer = 0;
    int play_multiplayer = 0;
    bool allow_draw = false;
    int play_multiplay_game = 0;
    signed int mum_x_pixel = 0;

    while (1)  {



        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
            game_over = my_global_values.game_over;
        }
        xSemaphoreGive(my_global_values.lock);


        if (DrawSignal) {
            if (xSemaphoreTake(DrawSignal, portMAX_DELAY) == pdTRUE) {

                tumEventFetchEvents(FETCH_EVENT_BLOCK |
                                    FETCH_EVENT_NO_GL_CHECK);
                xGetButtonInput();// Update global button data
                xSemaphoreTake(ScreenLock, portMAX_DELAY);

                checkDraw(tumDrawClear(White), __FUNCTION__);

                if (xSemaphoreTake(mothership_enemy.lock, 0) == pdTRUE) {
                    mum.x_pixel = mothership_enemy.mothership.x_pixel;
                    mum.y_pixel = mothership_enemy.mothership.y_pixel;
                    mum_x_pixel = mum.x_pixel;
                    mum.dead = mothership_enemy.mothership.dead;

                }
                xSemaphoreGive(mothership_enemy.lock);


                if (!mum.dead && allow_draw == true) {

                    checkDraw(tumDrawLoadedImage(mother, mum.x_pixel, mum.y_pixel), __FUNCTION__);

                }


                if (xSemaphoreTake(enemies.lock, 0) == pdTRUE) {
                    for (int i = 0; i < 5; i++) {
                        for (int j = 0; j < 8; j++) {


                            draw_x[i][j].x_pixel = enemies.enemy_position[i][j].x_pixel;
                            draw_x[i][j].y_pixel = enemies.enemy_position[i][j].y_pixel;
                            draw_x[i][j].dead = enemies.enemy_position[i][j].dead;

                        }

                    }
                }
                xSemaphoreGive(enemies.lock);

                for (int i = 0; i < 5; i++) {
                    for (int j = 0; j < 8; j++) {
                        if (allow_draw) {
                            if (i == 0) {
                                if (!draw_x[i][j].dead)

                                {
                                    checkDraw(tumDrawLoadedImage(monster2, draw_x[i][j].x_pixel, draw_x[i][j].y_pixel), __FUNCTION__);
                                }
                            }
                            else if (i == 1 || i == 2) {
                                if (!draw_x[i][j].dead) {
                                    checkDraw(tumDrawLoadedImage(monster1, draw_x[i][j].x_pixel, draw_x[i][j].y_pixel), __FUNCTION__);
                                }
                            }
                            else {
                                if (!draw_x[i][j].dead) {
                                    checkDraw(tumDrawLoadedImage(monster3, draw_x[i][j].x_pixel, draw_x[i][j].y_pixel), __FUNCTION__);
                                }
                            }
                        }
                    }
                }

                if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {
                    x_player = player1.x_pixel_of_player;
                    y_player = player1.y_pixel_of_player;
                    player_dead = player1.dead_of_player;
                }
                xSemaphoreGive(player1.lock);








                if (!player_dead && allow_draw)
                { tumDrawFilledBox(x_player, y_player, 18, 18, Red);}


                else if (player_dead && (start_game || play_multiplay_game)) {
                    if (my_Substract) {
                        vTaskSuspend(my_Substract);
                    }
                    if (move_player_right) {
                        vTaskSuspend(move_player_right);
                    }
                    sprintf(str2, "DEAD!!!");

                    checkDraw(tumDrawText(str2, x_player, y_player, Black),
                              __FUNCTION__);
                }
                else {

                }


                if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {
                    if (bullet_of_player.bullet_on) {
                        x_bullet_player = bullet_of_player.x_pixel_of_bullet;
                        y_bullet_player = bullet_of_player.y_pixel_of_bullet;
                        bullet_on_off = true;

                    }
                    else {

                        bullet_on_off = false;
                    }
                }
                xSemaphoreGive(bullet_of_player.lock);
                if (play_multiplay_game) {

                    if (previous_difficulty != difficulty) {
                        previous_difficulty = difficulty;
                    }

                    if (bullet_on_off_previous != bullet_on_off_previous) {
                        bullet_on_off_previous = bullet_on_off;
                    }
                    if (previous_pause_resumed_for_udp != pause_resumed_for_udp) {
                        previous_pause_resumed_for_udp = pause_resumed_for_udp;
                    }
                    if (x_player_previous != x_player || mum_x_pixel != mum_x_pixel_previous) {
                        x_player_previous = x_player;
                        mum_x_pixel_previous = mum_x_pixel;
                    }

                    xQueueSend(Pause_Resumed, (void *)&pause_resumed_for_udp, portMAX_DELAY);
                    if (pause_resumed_for_udp == true)
                    {  xQueueSend(Difficulty, (void *)&difficulty, portMAX_DELAY);}
                    if (pause_resumed_for_udp == true)
                    {xQueueSend(Bullet_active, (void *)&bullet_on_off, portMAX_DELAY);}
                    if (pause_resumed_for_udp == true)
                    {xQueueSend(X_player, (void *)&x_player, portMAX_DELAY);}
                    if (pause_resumed_for_udp == true)
                    {xQueueSend(Mothership_UDP, (void *)&mum_x_pixel, portMAX_DELAY);}



                }

                if (bullet_on_off && allow_draw) {
                    tumDrawFilledBox(x_bullet_player, y_bullet_player, 2, 10, Black);

                }



                if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {
                    if (bullet_of_enemy.bullet_on) {
                        x_bullet_enemy = bullet_of_enemy.x_pixel_of_bullet;
                        y_bullet_enemy = bullet_of_enemy.y_pixel_of_bullet;
                    }
                }
                xSemaphoreGive(bullet_of_enemy.lock);


                if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {
                    if (bullet_of_enemy.bullet_on || pause_pressed) {
                        if (allow_draw) {
                            tumDrawFilledBox(x_bullet_enemy + 10, y_bullet_enemy + 10, 2, 10, Red);
                        }
                    }

                }
                xSemaphoreGive(bullet_of_enemy.lock);


                if (xSemaphoreTake(green_blocks.lock, 0) == pdTRUE) {
                    for (int i = 0; i < 2; i++) {
                        for (int j = 0; j < 20; j++) {
                            save_blocks_positions[i][j].x_pixel_of_block = green_blocks.blocks_blocks[i][j].x_pixel_of_block;
                            save_blocks_positions[i][j].y_pixel_of_block = green_blocks.blocks_blocks[i][j].y_pixel_of_block;
                            save_blocks_positions[i][j].block_off = green_blocks.blocks_blocks[i][j].block_off;

                        }

                    }


                }
                xSemaphoreGive(green_blocks.lock);

                if (allow_draw) {
                    for (int i = 0; i < 2; i++) {
                        for (int j = 0; j < 20; j++) {
                            if (!save_blocks_positions[i][j].block_off) {
                                tumDrawFilledBox(save_blocks_positions[i][j].x_pixel_of_block, save_blocks_positions[i][j].y_pixel_of_block, 10, 10, Green);
                            }
                        }

                    }
                }

                if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                    lives = my_global_values.live;
                    level = my_global_values.level;
                    score = my_global_values.score;
                    highscore = my_global_values.highscore;
                    high_score_multiplayer = my_global_values.highscore_multiplayer;
                    killed_enemies = my_global_values.killed_enemies;

                }

                xSemaphoreGive(my_global_values.lock);



                if (killed_enemies == 40 && game_over == 0) {
                    sprintf(str9, "LOADING LEVEL: %d...", level + 2);
                    checkDraw(tumDrawText(str9, SCREEN_WIDTH / 2, SCREEN_HEIGHT / 2, Black),
                              __FUNCTION__);

                }
                if (game_over == 1) {
                    sprintf(str8, "GAME OVER");
                    checkDraw(tumDrawText(str8, SCREEN_WIDTH / 2, SCREEN_HEIGHT / 2, Black),
                              __FUNCTION__);


                }


                sprintf(str1, "LIVES: %d", lives);
                sprintf(str6, "MY SCORE: %d", score);
                sprintf(str7, "LEVEL: %d", level + 1);
                sprintf(str10, "START MENU");

                x_position_lives = 80;
                y_position_lives = SCREEN_HEIGHT - 20;





                if (start_game || play_multiplay_game) {
                    checkDraw(tumDrawText(str1, 10, SCREEN_HEIGHT - 20, Black),
                              __FUNCTION__);
                    for (int i = 0; i < lives; i++) {
                        tumDrawFilledBox(x_position_lives, y_position_lives, 10, 10, Red);
                        x_position_lives = x_position_lives + 20;
                    }

                    tumDrawFilledBox(0, SCREEN_HEIGHT - 28, SCREEN_WIDTH, 3, Black);


                    checkDraw(tumDrawText(str7, SCREEN_WIDTH - 120, SCREEN_HEIGHT - 70, Black), __FUNCTION__);

                    checkDraw(tumDrawText(str6, SCREEN_WIDTH - 120, SCREEN_HEIGHT - 90, Black), __FUNCTION__);

                    tumDrawFilledBox(SCREEN_WIDTH - 120, SCREEN_HEIGHT - 130, 110, 35, Red);
                    sprintf(str3, "PAUSE/RESUME");
                    checkDraw(tumDrawText(str3, SCREEN_WIDTH - 120, SCREEN_HEIGHT - 125, Black), __FUNCTION__);





                    if (game_over == 1) {
                        sprintf(str5, "PLAY AGAIN");
                    }
                    else {

                        sprintf(str5, "REPLAY");
                    }
                    tumDrawFilledBox(SCREEN_WIDTH - 120, SCREEN_HEIGHT - 170, 110, 35, Red);
                    checkDraw(tumDrawText(str5, SCREEN_WIDTH - 110, SCREEN_HEIGHT - 160, Black), __FUNCTION__);
                    tumDrawFilledBox(SCREEN_WIDTH - 120, SCREEN_HEIGHT - 210, 110, 35, Red);
                    checkDraw(tumDrawText(str10, SCREEN_WIDTH - 110, SCREEN_HEIGHT - 205, Black), __FUNCTION__);
                }




                if (!start_game && !start_game_multiplayer && !play_multiplay_game) {
                    sprintf(str16, "START MULTIPLAYER GAME");
                    sprintf(str4, "START SINGLE PLAYER GAME");
                    sprintf(str11, "INCREASE LIVES");
                    sprintf(str14, "SET STARTING SCORE");

                    tumDrawFilledBox(SCREEN_WIDTH / 2 - 50, SCREEN_HEIGHT / 2 - 40, 220, 35, Green);
                    checkDraw(tumDrawText(str16, SCREEN_WIDTH / 2 - 50 + 10, SCREEN_HEIGHT / 2 + -40 + 10, Black), __FUNCTION__);


                    //START GAME
                    tumDrawFilledBox(SCREEN_WIDTH / 2 - 50, SCREEN_HEIGHT / 2, 220, 35, Red);
                    checkDraw(tumDrawText(str4, SCREEN_WIDTH / 2 - 50 + 10, SCREEN_HEIGHT / 2 + 10, Black), __FUNCTION__);

                    tumDrawFilledBox(SCREEN_WIDTH / 2 - 50, SCREEN_HEIGHT / 2 + 40, 130, 35, Blue);
                    checkDraw(tumDrawText(str11, SCREEN_WIDTH / 2 - 50 + 10, SCREEN_HEIGHT / 2 + 40 + 10, Black), __FUNCTION__);

                    sprintf(str12, "%d", lives);

                    tumDrawFilledBox(SCREEN_WIDTH / 2 - 50 + 140, SCREEN_HEIGHT / 2 + 40, 35, 35, Yellow);
                    checkDraw(tumDrawText(str12, SCREEN_WIDTH / 2 - 50 + 140 + 10, SCREEN_HEIGHT / 2 + 40 + 10, Black), __FUNCTION__);



                    if (set_starting_score_pressed == 0) {
                        tumDrawFilledBox(SCREEN_WIDTH / 2 - 50, SCREEN_HEIGHT / 2 + 120, 170, 35, Green);
                        checkDraw(tumDrawText(str14, SCREEN_WIDTH / 2 - 50 + 10, SCREEN_HEIGHT / 2 + 130, Black), __FUNCTION__);
                    }
                    else {
                        if (one_number_pressed > 0) {
                            int ten_for_draw = 1;
                            int score_for_draw = 0;

                            for (int j = 0; j < one_number_pressed; j++) {


                                score_for_draw = score_for_draw + (array_for_set_starting_score[one_number_pressed - j - 1] * ten_for_draw);
                                ten_for_draw *= 10;
                            }
                            sprintf(str14, "%d ", score_for_draw);

                            tumDrawFilledBox(SCREEN_WIDTH / 2 - 50, SCREEN_HEIGHT / 2 + 120, 170, 35, Green);
                            checkDraw(tumDrawText(str14, SCREEN_WIDTH / 2 - 50 + 10, SCREEN_HEIGHT / 2 + 130, Black), __FUNCTION__);
                        }


                        else {
                            sprintf(str14, "TYPE,DELETE->LEFT");
                            tumDrawFilledBox(SCREEN_WIDTH / 2 - 50, SCREEN_HEIGHT / 2 + 120, 170, 35, Green);
                            checkDraw(tumDrawText(str14, SCREEN_WIDTH / 2 - 50 + 10, SCREEN_HEIGHT / 2 + 130, Black), __FUNCTION__);
                        }



                    }

                    if (see_high_level_pressed == 0) {
                        sprintf(str13, "SEE HIGHSCORE");
                        tumDrawFilledBox(SCREEN_WIDTH / 2 - 50, SCREEN_HEIGHT / 2 + 80, 130, 35, Orange);
                        checkDraw(tumDrawText(str13, SCREEN_WIDTH / 2 - 50 + 10, SCREEN_HEIGHT / 2 + 90, Black), __FUNCTION__);
                    }
                    else {
                        sprintf(str13, "%d", my_global_values.highscore);
                        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {

                            tumDrawFilledBox(SCREEN_WIDTH / 2 - 50, SCREEN_HEIGHT / 2 + 80, 130, 35, Orange);
                            checkDraw(tumDrawText(str13, SCREEN_WIDTH / 2 - 50 + 10, SCREEN_HEIGHT / 2 + 90, Black), __FUNCTION__);
                        }
                        xSemaphoreGive(my_global_values.lock);
                    }


                    if (tumEventGetMouseX() >= SCREEN_WIDTH / 2 - 50 && tumEventGetMouseX() <= SCREEN_WIDTH / 2 - 50 + 170) {
                        if (tumEventGetMouseY() >= SCREEN_HEIGHT / 2 + 120 && tumEventGetMouseY() <= SCREEN_HEIGHT / 2 + 120 + 35) {
                            printf("Set sarting score\n");

                            if (tumEventGetMouseLeft()) {
                                set_starting_score++;

                            }
                            if (!tumEventGetMouseLeft() && set_starting_score > 0) {
                                set_starting_score_pressed++;
                                set_starting_score = 0;
                                see_high_level_pressed = 0;
                            }

                        }

                    }




                    if (tumEventGetMouseX() >= SCREEN_WIDTH / 2 - 50 && tumEventGetMouseX() <= SCREEN_WIDTH / 2 - 50 + 130) {
                        if (tumEventGetMouseY() >= SCREEN_HEIGHT / 2 + 40 && tumEventGetMouseY() <= SCREEN_HEIGHT / 2 + 40 + 35) {
                            printf("Set lives\n");

                            if (tumEventGetMouseLeft()) {
                                increase_live++;
                            }

                            if (!tumEventGetMouseLeft() && increase_live > 0) {
                                increase_live_pressed++;
                                increase_live = 0;
                                see_high_level_pressed = 0;
                                set_starting_score_pressed = 0;
                                if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                                    my_global_values.live = my_global_values.live + 1;
                                }
                                xSemaphoreGive(my_global_values.lock);
                            }

                        }
                    }
                    if (tumEventGetMouseX() >= SCREEN_WIDTH / 2 - 50 && tumEventGetMouseX() <= SCREEN_WIDTH / 2 - 50 + 130) {

                        if (tumEventGetMouseY() >= SCREEN_HEIGHT / 2 + 80 && tumEventGetMouseY() <= SCREEN_HEIGHT / 2 + 80 + 35) {
                            printf("See highscore\n");

                            if (tumEventGetMouseLeft()) {
                                see_high_level++;

                            }
                            if (!tumEventGetMouseLeft() && see_high_level > 0) {
                                see_high_level = 0;
                                see_high_level_pressed++;
                                set_starting_score_pressed = 0;


                            }

                        }

                    }
                    if (set_starting_score_pressed > 0) {
                        if (xSemaphoreTake(buttons.lock, 0) == pdTRUE) {
                            if (buttons.buttons[KEYCODE(0)]) {
                                zero++;
                            }
                            if (!buttons.buttons[KEYCODE(0)] && zero > 0) {
                                zero = 0;
                                zero_pressed++;
                                one_number_pressed++;
                                printf("PRESSED\n");
                                printf("%d\n", one_number_pressed);
                            }
                            if (buttons.buttons[KEYCODE(1)]) {
                                one++;
                            }
                            if (!buttons.buttons[KEYCODE(1)] && one > 0) {
                                one = 0;
                                one_pressed++;
                                one_number_pressed++;
                                printf("PRESSED\n");
                                printf("%d\n", one_number_pressed);
                            }
                            if (buttons.buttons[KEYCODE(2)]) {
                                two++;
                            }
                            if (!buttons.buttons[KEYCODE(2)] && two > 0) {
                                two = 0;
                                two_pressed++;
                                one_number_pressed++;
                                printf("PRESSED\n");
                                printf("%d\n", one_number_pressed);
                            }
                            if (buttons.buttons[KEYCODE(3)]) {
                                three++;
                            }
                            if (!buttons.buttons[KEYCODE(3)] && three > 0) {
                                three = 0;
                                three_pressed++;
                                one_number_pressed++;
                                printf("PRESSED\n");
                                printf("%d\n", one_number_pressed);
                            }
                            if (buttons.buttons[KEYCODE(4)]) {
                                four++;
                            }
                            if (!buttons.buttons[KEYCODE(4)] && four > 0) {
                                four = 0;
                                four_pressed++;
                                one_number_pressed++;
                                printf("PRESSED\n");
                                printf("%d\n", one_number_pressed);
                            }
                            if (buttons.buttons[KEYCODE(5)]) {
                                five++;
                            }
                            if (!buttons.buttons[KEYCODE(5)] && five > 0) {
                                five = 0;
                                five_pressed++;
                                one_number_pressed++;
                                printf("PRESSED\n");
                                printf("%d\n", one_number_pressed);
                            }
                            if (buttons.buttons[KEYCODE(6)]) {
                                six++;
                            }
                            if (!buttons.buttons[KEYCODE(6)] && six > 0) {
                                six = 0;
                                six_pressed++;
                                one_number_pressed++;
                                printf("PRESSED\n");
                                printf("%d\n", one_number_pressed);
                            }
                            if (buttons.buttons[KEYCODE(7)]) {
                                seven++;
                            }
                            if (!buttons.buttons[KEYCODE(7)] && seven > 0) {
                                seven = 0;
                                seven_pressed++;
                                one_number_pressed++;
                                printf("PRESSED\n");
                                printf("%d\n", one_number_pressed);
                            }
                            if (buttons.buttons[KEYCODE(8)]) {
                                eight++;
                            }
                            if (!buttons.buttons[KEYCODE(8)] && eight > 0) {
                                eight = 0;
                                eight_pressed++;
                                one_number_pressed++;
                                printf("PRESSED\n");
                                printf("%d\n", one_number_pressed);
                            }
                            if (buttons.buttons[KEYCODE(9)])

                            {
                                nine++;
                            }
                            if (!buttons.buttons[KEYCODE(9)] && nine > 0) {
                                nine = 0;
                                nine_pressed++;
                                one_number_pressed++;
                                printf("PRESSED\n");
                                printf("%d\n", one_number_pressed);
                            }
                            if (buttons.buttons[KEYCODE(LEFT)] && one_number_pressed != 0) {
                                clear++;
                            }
                            if (!buttons.buttons[KEYCODE(LEFT)] && clear > 0) {
                                clear_pressed++;
                                clear = 0;

                                printf("Aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n");

                            }

                        }
                        xSemaphoreGive(buttons.lock);



                    }
                    if (zero_pressed) {

                        array_for_set_starting_score[one_number_pressed - 1] = 0;
                        zero_pressed = 0;
                        printf("One number: %d\n", one_number_pressed);
                        printf("array_for_set_starting_score[%d]=%d\n", one_number_pressed - 1, array_for_set_starting_score[one_number_pressed - 1]);

                    }
                    if (one_pressed) {

                        array_for_set_starting_score[one_number_pressed - 1] = 1;
                        one_pressed = 0;
                        printf("One number: %d\n", one_number_pressed);
                        printf("array_for_set_starting_score[%d]=%d\n", one_number_pressed - 1, array_for_set_starting_score[one_number_pressed - 1]);
                    }
                    if (two_pressed) {
                        array_for_set_starting_score[one_number_pressed - 1] = 2;
                        two_pressed = 0;
                        printf("One number: %d\n", one_number_pressed);
                        printf("array_for_set_starting_score[%d]=%d\n", one_number_pressed - 1, array_for_set_starting_score[one_number_pressed - 1]);
                    }
                    if (three_pressed) {
                        array_for_set_starting_score[one_number_pressed - 1] = 3;
                        three_pressed = 0;
                        printf("One number: %d\n", one_number_pressed);
                        printf("array_for_set_starting_score[%d]=%d\n", one_number_pressed - 1, array_for_set_starting_score[one_number_pressed - 1]);
                    }
                    if (four_pressed) {
                        array_for_set_starting_score[one_number_pressed - 1] = 4;
                        four_pressed = 0;
                        printf("One number: %d\n", one_number_pressed);
                        printf("array_for_set_starting_score[%d]=%d\n", one_number_pressed - 1, array_for_set_starting_score[one_number_pressed - 1]);
                    }
                    if (five_pressed) {
                        array_for_set_starting_score[one_number_pressed - 1] = 5;
                        five_pressed = 0;
                        printf("One number: %d\n", one_number_pressed);
                        printf("array_for_set_starting_score[%d]=%d\n", one_number_pressed - 1, array_for_set_starting_score[one_number_pressed - 1]);
                    }
                    if (six_pressed) {
                        array_for_set_starting_score[one_number_pressed - 1] = 6;
                        six_pressed = 0;
                        printf("One number: %d\n", one_number_pressed);
                        printf("array_for_set_starting_score[%d]=%d\n", one_number_pressed - 1, array_for_set_starting_score[one_number_pressed - 1]);
                    }
                    if (seven_pressed) {
                        array_for_set_starting_score[one_number_pressed - 1] = 7;
                        seven_pressed = 0;
                        printf("One number: %d\n", one_number_pressed);
                        printf("array_for_set_starting_score[%d]=%d\n", one_number_pressed - 1, array_for_set_starting_score[one_number_pressed - 1]);
                    }
                    if (eight_pressed) {
                        array_for_set_starting_score[one_number_pressed - 1] = 8;
                        eight_pressed = 0;
                        printf("One number: %d\n", one_number_pressed);
                        printf("array_for_set_starting_score[%d]=%d\n", one_number_pressed - 1, array_for_set_starting_score[one_number_pressed]);
                    }
                    if (nine_pressed) {
                        array_for_set_starting_score[one_number_pressed - 1] = 9;
                        nine_pressed = 0;
                        printf("One number: %d\n", one_number_pressed);
                        printf("array_for_set_starting_score[%d]=%d\n", one_number_pressed - 1, array_for_set_starting_score[one_number_pressed - 1]);
                    }
                    if (clear_pressed) {
                        clear_pressed = 0;
                        one_number_pressed--;
                    }



                    //PRESS START SINGLE PLAYER

                    if (tumEventGetMouseX() >= SCREEN_WIDTH / 2 - 50 && tumEventGetMouseX() <= SCREEN_WIDTH / 2 + 220 - 50 && start_game == 0 && start_game_multiplayer == 0) {
                        if (tumEventGetMouseY() >= SCREEN_HEIGHT / 2 && tumEventGetMouseY() <= SCREEN_HEIGHT / 2 + 35) {
                            printf("Start game\n");
                            if (tumEventGetMouseLeft() && increase_live == 0) {

                                start_game = 1;
                                allow_draw = true;

                                int ten = 1;
                                time_pressed_pause = 0;
                                see_high_level_pressed = 0;
                                set_starting_score_pressed = 0;


                                for (int j = 0; j < one_number_pressed; j++) {

                                    if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                                        my_global_values.score = my_global_values.score + (array_for_set_starting_score[one_number_pressed - j - 1] * ten);
                                        ten *= 10;
                                    }
                                    xSemaphoreGive(my_global_values.lock);
                                }
                                one_number_pressed = 0;


                                if (positions) {
                                    vTaskResume(positions);
                                }
                                if (help_to_positions_of_enemy) {
                                    vTaskResume(help_to_positions_of_enemy);
                                }
                                if (mothership_on_off) {
                                    vTaskResume(mothership_on_off);
                                }

                            }


                        }

                    }


                    if (tumEventGetMouseX() >= SCREEN_WIDTH / 2 - 50 && tumEventGetMouseX() <= SCREEN_WIDTH / 2 + 220 - 50) {
                        if (tumEventGetMouseY() >= SCREEN_HEIGHT / 2 - 40 && tumEventGetMouseY() <= SCREEN_HEIGHT / 2 - 40 + 35) {
                            if (tumEventGetMouseLeft() && increase_live == 0) {
                                left_mouse = true;
                            }
                            if (!tumEventGetMouseLeft() && left_mouse == true) {
                                left_mouse = false;
                                start_game_multiplayer = 1;
                                int ten = 1;
                                time_pressed_pause = 0;
                                see_high_level_pressed = 0;
                                set_starting_score_pressed = 0;



                                for (int j = 0; j < one_number_pressed; j++) {

                                    if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                                        my_global_values.multiplay_game = true;
                                        my_global_values.score = my_global_values.score + (array_for_set_starting_score[one_number_pressed - j - 1] * ten);
                                        ten *= 10;
                                    }
                                    xSemaphoreGive(my_global_values.lock);
                                }
                                one_number_pressed = 0;
                                if (control_Multiplayer) {
                                    vTaskResume(control_Multiplayer);
                                }


                            }


                        }


                    }
                }






                if (start_game_multiplayer == 1) {


                    sprintf(str17, "BACK");

                    tumDrawFilledBox(SCREEN_WIDTH / 2 - 50, SCREEN_HEIGHT / 2, 60, 35, Red);
                    checkDraw(tumDrawText(str17, SCREEN_WIDTH / 2 - 50 + 10, SCREEN_HEIGHT / 2 + 10, Black), __FUNCTION__);

                    sprintf(str18, "PLAY");
                    tumDrawFilledBox(SCREEN_WIDTH / 2 - 50, SCREEN_HEIGHT / 2 - 40, 60, 35, Red);
                    checkDraw(tumDrawText(str18, SCREEN_WIDTH / 2 - 50 + 10, SCREEN_HEIGHT / 2 - 40 + 10, Black), __FUNCTION__);

                    sprintf(str19, "D%d", difficulty + 1);
                    tumDrawFilledBox(SCREEN_WIDTH / 2 - 50, SCREEN_HEIGHT / 2 + 40, 60, 35, Red);
                    checkDraw(tumDrawText(str19, SCREEN_WIDTH / 2 - 50 + 10, SCREEN_HEIGHT / 2 + 40 + 10, Black), __FUNCTION__);
                    sprintf(str20, "+");
                    tumDrawFilledBox(SCREEN_WIDTH / 2 - 50 + 70, SCREEN_HEIGHT / 2 + 40, 35, 35, Red);
                    checkDraw(tumDrawText(str20, SCREEN_WIDTH / 2 - 50 + 80, SCREEN_HEIGHT / 2 + 40 + 10, Black), __FUNCTION__);

                    if (tumEventGetMouseX() >= SCREEN_WIDTH / 2 - 50 && tumEventGetMouseX() <= SCREEN_WIDTH / 2 - 50 + 60) {
                        if (tumEventGetMouseY() >= SCREEN_HEIGHT / 2 - 40 && tumEventGetMouseY() <= SCREEN_HEIGHT / 2 - 40 + 35) {
                            printf("Play\n");
                            if (tumEventGetMouseLeft()) {
                                left_mouse = true;
                            }
                            if (!tumEventGetMouseLeft() && left_mouse) {
                                printf("SSSSSSSSSSSSSSSS\n");

                                left_mouse = false;
                                start_game_multiplayer = 0;

                                allow_draw = true;
                                if (xSemaphoreTake(mothership_enemy.lock, 0) == pdTRUE) {
                                    mothership_enemy.multiplay_game = true;
                                }
                                xSemaphoreGive(mothership_enemy.lock);

                                play_multiplay_game = 1;
                                pause_resumed_for_udp = true;
                                if (positions)
                                {vTaskResume(positions);}

                                if (help_to_positions_of_enemy) {
                                    vTaskResume(help_to_positions_of_enemy);
                                }

                                if (control_Multiplayer) {
                                    vTaskResume(control_Multiplayer);
                                }
                                if (mothership_multiplayer) {
                                    vTaskResume(mothership_multiplayer);
                                }




                            }
                        }

                    }



                    if (tumEventGetMouseX() >= SCREEN_WIDTH / 2 - 50 + 70 && tumEventGetMouseX() <= SCREEN_WIDTH / 2 - 50 + 70 + 35) {
                        if (tumEventGetMouseY() >= SCREEN_HEIGHT / 2 + 40 && tumEventGetMouseY() <= SCREEN_HEIGHT / 2 + 40 + 35) {
                            if (tumEventGetMouseLeft()) {
                                left_mouse = true;
                            }
                            if (!tumEventGetMouseLeft() && left_mouse == true) {
                                left_mouse = false;
                                difficulty = (difficulty + 1) % 3;
                                printf("Difficulty\n");


                            }
                        }
                    }
                    if (tumEventGetMouseX() >= SCREEN_WIDTH / 2 - 50 && tumEventGetMouseX() <= SCREEN_WIDTH / 2 - 50 + 60) {
                        if (tumEventGetMouseY() >= SCREEN_HEIGHT / 2 && tumEventGetMouseY() <= SCREEN_HEIGHT / 2 + 35) {
                            printf("BACK\n");
                            if (tumEventGetMouseLeft()) {

                                left_mouse = true;

                            }
                            if (!tumEventGetMouseLeft() && left_mouse == true) {
                                left_mouse = false;
                                start_game_multiplayer = 0;
                                difficulty = 2;
                                play_multiplay_game = 0;
                                pause_resumed_for_udp = false;
                                if (positions)
                                {vTaskSuspend(positions);}

                                if (help_to_positions_of_enemy) {
                                    vTaskSuspend(help_to_positions_of_enemy);
                                }
                                if (mothership_multiplayer) {
                                    vTaskSuspend(mothership_multiplayer);
                                }
                                if (control_Multiplayer) {
                                    vTaskSuspend(control_Multiplayer);
                                }




                            }

                        }

                    }
                }


















                if (tumEventGetMouseX() >= SCREEN_WIDTH - 120 && tumEventGetMouseX() <= SCREEN_WIDTH - 10 && (start_game == 1 || play_multiplay_game)) {
                    if (tumEventGetMouseY() >= SCREEN_HEIGHT - 210 && tumEventGetMouseY() <= SCREEN_HEIGHT - 175) {
                        if (tumEventGetMouseLeft() == 1) {
                            if (!go_back) {

                                go_back++;
                            }
                        }
                    }
                }


                if (tumEventGetMouseX() >= SCREEN_WIDTH - 120 && tumEventGetMouseX() <= SCREEN_WIDTH - 10 && (start_game == 1 || play_multiplay_game)) {
                    if (tumEventGetMouseY() >= SCREEN_HEIGHT - 170 && tumEventGetMouseY() <= SCREEN_HEIGHT - 135) {
                        if (tumEventGetMouseLeft() == 1) {
                            if (!replay) {
                                replay++;
                            }


                        }
                    }
                }

                if (tumEventGetMouseX() >= SCREEN_WIDTH - 120 && tumEventGetMouseX() <= SCREEN_WIDTH - 10 && (start_game == 1 || play_multiplay_game == 1) && game_over == 0) {
                    if (tumEventGetMouseY() >= SCREEN_HEIGHT - 130 && tumEventGetMouseY() <= SCREEN_HEIGHT - 95) {
                        if (tumEventGetMouseLeft() == 1) {
                            if (!pause_pressed) {

                                pause_pressed++;
                            }

                        }
                        if (!tumEventGetMouseLeft() && pause_pressed > 0) {
                            pause_pressed = 0;
                            pause_resume++;

                        }

                    }
                }

                //PAUSE RESUME

                if (pause_resume > 0 && !tumEventGetMouseLeft() && game_over == 0) {
                    int reset_value = 0;
                    pause_resume = 0;
                    time_pressed_pause++;

                    printf("TIME PRESSED PAUSE: %d\n", time_pressed_pause);



                    if (time_pressed_pause % 2) {
                        if (start_game == 1 && play_multiplay_game == 0) {
                            if (mothership_on_off) {
                                vTaskSuspend(mothership_on_off);
                            }
                            if (mothership) {
                                vTaskSuspend(mothership);

                            }
                        }
                        else {
                            if (play_multiplay_game == 1) {

                                pause_resumed_for_udp = false;
                                if (mothership_multiplayer) {
                                    vTaskSuspend(mothership_multiplayer);
                                }

                            }
                        }


                        if (move_player_right) {
                            vTaskSuspend(move_player_right);
                        }

                        if (my_Substract) {
                            vTaskSuspend(my_Substract);
                        }

                        if (positions) {
                            vTaskSuspend(positions);
                        }

                        if (help_to_positions_of_enemy) {
                            vTaskSuspend(help_to_positions_of_enemy);
                        }


                        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                            if (my_global_values.killed_enemies == 40) {
                                my_global_values.pressed_pause = 1;

                            }

                        }
                        xSemaphoreGive(my_global_values.lock);


                        if (enemy_bullet) {
                            vTaskSuspend(enemy_bullet);
                        }




                        if (bullet_of_player_task)
                        {vTaskSuspend(bullet_of_player_task);}

                        if (show_text_dead_player) {
                            vTaskSuspend(show_text_dead_player);
                        }



                    }





                    else {
                        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                            if (my_global_values.give_new_values == 1) {
                                my_global_values.give_new_values = 0;
                                my_global_values.pressed_pause = 0;
                                my_global_values.level = my_global_values.level + 1;
                                my_global_values.right = 0;
                                my_global_values.left = 1000;
                                my_global_values.five = 10;
                                my_global_values.live = 3;
                                my_global_values.change_position = 0;
                                my_global_values.seconds = 0;
                                my_global_values.y = 0;
                                my_global_values.killed_enemies = 0;
                                my_global_values.speed = 400 - (my_global_values.level * 50);
                                my_global_values.game_over = 0;
                                my_global_values.pressed_replay = 0;
                                my_global_values.give_new_replay = 0;
                                reset_value = 1;
                            }

                        }

                        xSemaphoreGive(my_global_values.lock);
                        if (reset_value == 1)

                        {
                            reset_value = 0;
                            if (xSemaphoreTake(mothership_enemy.lock, 0) == pdTRUE)

                            {
                                mothership_enemy.mothership.x_pixel = -20;
                                mothership_enemy.mothership.y_pixel = 2;
                                mothership_enemy.mothership.dead = 0;

                            }
                            xSemaphoreGive(mothership_enemy.lock);
                            if (xSemaphoreTake(enemies.lock, 0) == pdTRUE) {
                                for (int i = 0; i < 5; i++) {
                                    for (int j = 0; j < 8; j++) {
                                        enemies.enemy_position[i][j].dead = 0;
                                        enemies.enemy_position[i][j].x_pixel = 0;
                                        enemies.enemy_position[i][j].y_pixel = 0;
                                    }

                                }
                            }
                            xSemaphoreGive(enemies.lock);
                            if (xSemaphoreTake(green_blocks.lock, 0) == pdTRUE) {
                                for (int i = 0; i < 2; i++) {
                                    for (int j = 0; j < 20; j++) {
                                        green_blocks.blocks_blocks[i][j].block_off = 0;
                                    }
                                }
                            }
                            xSemaphoreGive(green_blocks.lock);
                            if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {
                                bullet_of_enemy.bullet_on = 0;
                                bullet_of_enemy.position_take = 0;

                            }
                            xSemaphoreGive(bullet_of_enemy.lock);

                            if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {
                                bullet_of_player.dead_player = 0;
                                bullet_of_player.bullet_on = 0;
                                bullet_of_player.position_take = 0;
                                bullet_of_player.x_pixel_of_bullet = SCREEN_WIDTH / 2 + 10;
                                bullet_of_player.y_pixel_of_bullet = SCREEN_HEIGHT - 50;
                            }
                            xSemaphoreGive(bullet_of_player.lock);



                            if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {
                                player1.dead_of_player = 0;
                                player1.bullet_on_off = 0;
                                player1.position_take = 0;
                                player1.x_pixel_of_player = SCREEN_WIDTH / 2;
                                player1.y_pixel_of_player = SCREEN_HEIGHT - 50;
                            }
                            xSemaphoreGive(player1.lock);
                        }







                        if (positions) {
                            vTaskResume(positions);
                        }
                        if (help_to_positions_of_enemy) {
                            vTaskResume(help_to_positions_of_enemy);
                        }

                        if (start_game) {
                            if (mothership_on_off) {
                                vTaskResume(mothership_on_off);
                            }
                            if (xSemaphoreTake(mothership_enemy.lock, 0) == pdTRUE) {
                                if (!mothership_enemy.mothership.dead) {
                                    vTaskResume(mothership);
                                }
                            }
                            xSemaphoreGive(mothership_enemy.lock);

                        }
                        if (play_multiplay_game == 1) {
                            pause_resumed_for_udp = true;
                            if (mothership_multiplayer) {
                                vTaskResume(mothership_multiplayer);
                            }

                        }



                        if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {
                            if (bullet_of_enemy.bullet_on) {
                                if (enemy_bullet) {
                                    vTaskResume(enemy_bullet);
                                }
                            }

                        }
                        xSemaphoreGive(bullet_of_enemy.lock);



                        if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {
                            if (bullet_of_player.bullet_on)
                                if (bullet_of_player_task) {
                                    vTaskResume(bullet_of_player_task);
                                }
                        }
                        xSemaphoreGive(bullet_of_player.lock);
                        if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {
                            if (player1.dead_of_player == 1) {
                                vTaskResume(show_text_dead_player);
                            }
                        }
                        xSemaphoreGive(player1.lock);
                    }
                }


                //REPLAY WITHOUT PAUSE










                if (!tumEventGetMouseLeft() && time_pressed_pause % 2 == 0 && replay > 0 && game_over == 0) {
                    replay = 0;
                    int resume = 0;
                    bool lives_back = false;



                    if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                        if (my_global_values.killed_enemies == 40 && my_global_values.pressed_replay == 0) {
                            my_global_values.pressed_replay = 1;
                            replay++;
                            printf("111111111111111111111waaaaaaaaaaitttttttttting\n");

                        }
                        else {
                            resume = 1;
                            printf("11111111111111111111111111111Diiiiiiiiiireeeeeeeeeeect");

                        }
                        if (my_global_values.give_new_replay == 1) {
                            resume = 1;
                            my_global_values.pressed_replay = 0;
                            my_global_values.give_new_replay = 0;
                            my_global_values.give_new_values = 0;
                            my_global_values.pressed_pause = 0;
                            printf("111111111111111111111Doooooooooneeeeeeeeeeee\n");
                            printf("\n");

                        }
                    }
                    xSemaphoreGive(my_global_values.lock);

                    if (resume) {


                        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                            my_global_values.level = 0;
                            my_global_values.score = 0;
                            my_global_values.right = 0;
                            my_global_values.left = 1000;
                            my_global_values.five = 10;
                            my_global_values.live = 3;
                            my_global_values.change_position = 0;
                            my_global_values.seconds = 0;
                            my_global_values.y = 0;
                            my_global_values.killed_enemies = 0;
                            my_global_values.speed = 400;
                            my_global_values.game_over = 0;

                        }
                        xSemaphoreGive(my_global_values.lock);
                        if (xSemaphoreTake(mothership_enemy.lock, 0) == pdTRUE) {
                            mothership_enemy.mothership.x_pixel = -20;
                            mothership_enemy.mothership.y_pixel = 2;
                            if (mothership_enemy.mothership.dead == 0 && mothership_enemy.collision_happend == 1)
                            {mothership_enemy.collision_happend = 1;}

                        }
                        xSemaphoreGive(mothership_enemy.lock);
                        if (xSemaphoreTake(enemies.lock, 0) == pdTRUE) {
                            for (int i = 0; i < 5; i++) {
                                for (int j = 0; j < 8; j++) {
                                    enemies.enemy_position[i][j].dead = 0;
                                    enemies.enemy_position[i][j].x_pixel = 0;
                                    enemies.enemy_position[i][j].y_pixel = 0;
                                }

                            }
                        }
                        xSemaphoreGive(enemies.lock);
                        if (xSemaphoreTake(green_blocks.lock, 0) == pdTRUE) {
                            for (int i = 0; i < 2; i++) {
                                for (int j = 0; j < 20; j++) {
                                    green_blocks.blocks_blocks[i][j].block_off = 0;
                                }
                            }
                        }
                        xSemaphoreGive(green_blocks.lock);
                        if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {
                            if (bullet_of_enemy.bullet_on == 1 && bullet_of_enemy.collision_happend == 0) {
                                bullet_of_enemy.collision_happend = 1;
                            }


                        }
                        xSemaphoreGive(bullet_of_enemy.lock);

                        if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {


                            if (bullet_of_player.bullet_on == 1 && bullet_of_player.collision_happend == 0) {
                                bullet_of_player.collision_happend = 1;
                            }

                            bullet_of_player.x_pixel_of_bullet = SCREEN_WIDTH / 2 + 10;
                            bullet_of_player.y_pixel_of_bullet = SCREEN_HEIGHT - 50;
                            bullet_of_player.position_take = 0;
                        }
                        xSemaphoreGive(bullet_of_player.lock);


                        if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {

                            if (player1.dead_of_player == 1) {
                                player1.break_show_text_dead_player = 1;
                                lives_back = true;
                            }
                            player1.x_pixel_of_player = SCREEN_WIDTH / 2;
                            player1.y_pixel_of_player = SCREEN_HEIGHT - 50;
                            player1.position_take = 0;


                        }
                        xSemaphoreGive(player1.lock);

                    }



                    if (positions) {
                        vTaskResume(positions);
                    }
                    if (help_to_positions_of_enemy) {
                        vTaskResume(help_to_positions_of_enemy);
                    }
                    if (start_game) {
                        if (mothership) {
                            vTaskResume(mothership);
                        }
                    }
                    if (play_multiplay_game) {
                        if (mothership_multiplayer)
                        { vTaskResume(mothership_multiplayer);}
                        if (control_Multiplayer)
                        {  vTaskResume(control_Multiplayer);}
                    }

                    if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                        if (lives_back) {
                            my_global_values.live = 4;
                        }

                    }
                    xSemaphoreGive(my_global_values.lock);


                }

                //REPLAY WITH PAUSE AND RESUME

                if (!tumEventGetMouseLeft() && time_pressed_pause % 2 == 1 && replay > 0) {


                    bool lives_back = false;
                    replay = 0;
                    int resume = 0;
                    //IN THE ANOTHER CASE GOES IN GAME OVER LOOK REPEATLY AND SUSPEND EVERYTHING, WITHOUT game_over = 0;
                    game_over = 0;

                    if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                        if (my_global_values.killed_enemies == 40) {
                            if (my_global_values.give_new_values == 1) {
                                my_global_values.give_new_replay = 0;
                                my_global_values.give_new_values = 0;
                                my_global_values.pressed_pause = 0;
                                my_global_values.pressed_replay = 0;
                                printf("222222222222222222222222222222222222Dooneeee\n");

                                resume = 1;
                            }
                            else {
                                printf("22222222222222222222222222222222waaaaaaaaaaaaaaiiiiiiiiiiiit\n");
                                replay++;
                            }
                        }
                        else {
                            resume = 1;
                            printf("22222222222222222222222222Diiiiiiiiiireeeeeeeeeeeeecttttttt\n");

                        }

                    }
                    xSemaphoreGive(my_global_values.lock);

                    if (resume)

                    {
                        resume = 0;
                        time_pressed_pause = 0;



                        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                            my_global_values.level = 0;
                            my_global_values.score = 0;
                            my_global_values.right = 0;
                            my_global_values.left = 1000;
                            my_global_values.five = 10;
                            my_global_values.live = 3;
                            my_global_values.change_position = 0;
                            my_global_values.seconds = 0;
                            my_global_values.y = 0;
                            my_global_values.killed_enemies = 0;
                            my_global_values.speed = 400;
                            my_global_values.game_over = 0;




                        }
                        xSemaphoreGive(my_global_values.lock);


                        if (xSemaphoreTake(mothership_enemy.lock, 0) == pdTRUE)

                        {
                            mothership_enemy.mothership.x_pixel = -20;
                            mothership_enemy.mothership.y_pixel = 2;
                            mothership_enemy.mothership.dead = 0;
                            mothership_enemy.collision_happend = 0;
                            if (mothership_enemy.multiplay_game == true) {
                                pause_resumed_for_udp = true;
                            }

                        }
                        xSemaphoreGive(mothership_enemy.lock);
                        if (xSemaphoreTake(enemies.lock, 0) == pdTRUE) {
                            for (int i = 0; i < 5; i++) {
                                for (int j = 0; j < 8; j++) {
                                    enemies.enemy_position[i][j].dead = 0;
                                    enemies.enemy_position[i][j].x_pixel = 0;
                                    enemies.enemy_position[i][j].y_pixel = 0;
                                }

                            }
                        }
                        xSemaphoreGive(enemies.lock);
                        if (xSemaphoreTake(green_blocks.lock, 0) == pdTRUE) {
                            for (int i = 0; i < 2; i++) {
                                for (int j = 0; j < 20; j++) {
                                    green_blocks.blocks_blocks[i][j].block_off = 0;
                                }
                            }
                        }
                        xSemaphoreGive(green_blocks.lock);
                        if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {
                            bullet_of_enemy.collision_happend = 0;
                            bullet_of_enemy.position_take = 0;
                            bullet_of_enemy.bullet_on = 0;



                        }
                        xSemaphoreGive(bullet_of_enemy.lock);

                        if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {
                            bullet_of_player.position_take = 0;
                            bullet_of_player.bullet_on = 0;
                            bullet_of_player.collision_happend = 0;
                            bullet_of_player.x_pixel_of_bullet = SCREEN_WIDTH / 2 + 10;
                            bullet_of_player.y_pixel_of_bullet = SCREEN_HEIGHT - 50;

                        }
                        xSemaphoreGive(bullet_of_player.lock);



                        if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {
                            if (player1.dead_of_player == 1) {
                                vTaskResume(show_text_dead_player);
                                player1.break_show_text_dead_player = 1;
                                lives_back = true;
                                printf("Replay after dead from player\n");
                            }
                            player1.x_pixel_of_player = SCREEN_WIDTH / 2;
                            player1.y_pixel_of_player = SCREEN_HEIGHT - 50;
                            player1.position_take = 0;
                        }
                        xSemaphoreGive(player1.lock);


                    }



                    if (positions) {
                        vTaskResume(positions);

                    }
                    if (help_to_positions_of_enemy) {
                        vTaskResume(help_to_positions_of_enemy);
                    }

                    if (start_game_multiplayer == true) {
                        if (mothership_on_off) {
                            vTaskResume(mothership_on_off);
                        }
                    }
                    else {
                        if (mothership_multiplayer)

                        {vTaskResume(mothership_multiplayer);}

                        if (control_Multiplayer)
                        { vTaskResume(control_Multiplayer);}
                    }

                    if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                        if (lives_back) {
                            my_global_values.live = 4;
                        }

                    }
                    xSemaphoreGive(my_global_values.lock);

                }

                //GO BACK TO START MENU WITHOUT POUSE

                if (!tumEventGetMouseLeft() && go_back > 0 && time_pressed_pause % 2 == 0) {
                    go_back = 0;
                    start_game = 0;
                    int resume = 0;
                    allow_draw = false;
                    bool lives_back = false;

                    if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                        if (my_global_values.killed_enemies == 40 && my_global_values.pressed_replay == 0) {
                            my_global_values.pressed_replay = 1;
                            go_back++;
                            printf("BBBBBBBBBBBBBBBBBBBB111111111111111111111waaaaaaaaaaitttttttttting\n");

                        }
                        else {
                            resume = 1;
                            printf("BBBBBBBBBBBBBBBBBBBBBB11111111111111111111111111111Diiiiiiiiiireeeeeeeeeeect");

                        }
                        if (my_global_values.give_new_replay == 1) {
                            resume = 1;
                            my_global_values.pressed_replay = 0;
                            my_global_values.give_new_replay = 0;
                            my_global_values.give_new_values = 0;
                            my_global_values.pressed_pause = 0;
                            printf("BBBBBBBBBBBBBBBBBBBBBBBBBBB111111111111111111111Doooooooooneeeeeeeeeeee\n");
                            printf("\n");

                        }
                    }
                    xSemaphoreGive(my_global_values.lock);


                    if (resume) {


                        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                            my_global_values.level = 0;
                            my_global_values.score = 0;
                            my_global_values.right = 0;
                            my_global_values.left = 1000;
                            my_global_values.five = 10;
                            my_global_values.live = 3;
                            my_global_values.change_position = 0;
                            my_global_values.seconds = 0;
                            my_global_values.y = 0;
                            my_global_values.killed_enemies = 0;
                            my_global_values.speed = 400;
                            my_global_values.game_over = 0;

                        }
                        xSemaphoreGive(my_global_values.lock);
                        if (xSemaphoreTake(mothership_enemy.lock, 0) == pdTRUE) {
                            mothership_enemy.mothership.x_pixel = -20;
                            mothership_enemy.mothership.y_pixel = 2;
                            if (mothership_enemy.mothership.dead == 0 && mothership_enemy.collision_happend == 0) {
                                mothership_enemy.collision_happend = 1;
                            }
                            if (mothership_enemy.multiplay_game == true) {
                                mothership_enemy.multiplay_game = false;
                                play_multiplay_game = 0;
                                difficulty = 1;
                            }

                        }
                        xSemaphoreGive(mothership_enemy.lock);
                        if (xSemaphoreTake(enemies.lock, 0) == pdTRUE) {
                            for (int i = 0; i < 5; i++) {
                                for (int j = 0; j < 8; j++) {
                                    enemies.enemy_position[i][j].dead = 0;
                                    enemies.enemy_position[i][j].x_pixel = 0;
                                    enemies.enemy_position[i][j].y_pixel = 0;
                                }

                            }
                        }
                        xSemaphoreGive(enemies.lock);
                        if (xSemaphoreTake(green_blocks.lock, 0) == pdTRUE) {
                            for (int i = 0; i < 2; i++) {
                                for (int j = 0; j < 20; j++) {
                                    green_blocks.blocks_blocks[i][j].block_off = 0;
                                }
                            }
                        }
                        xSemaphoreGive(green_blocks.lock);
                        if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {
                            if (bullet_of_enemy.bullet_on == 1 && bullet_of_enemy.collision_happend == 0) {
                                bullet_of_enemy.collision_happend = 1;
                            }

                        }
                        xSemaphoreGive(bullet_of_enemy.lock);

                        if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {

                            if (bullet_of_player.bullet_on == 1 && bullet_of_player.collision_happend == 0) {
                                bullet_of_player.collision_happend = 0;
                            }
                            bullet_of_player.x_pixel_of_bullet = SCREEN_WIDTH / 2 + 10;
                            bullet_of_player.y_pixel_of_bullet = SCREEN_HEIGHT - 50;
                            bullet_of_player.position_take = 0;
                        }
                        xSemaphoreGive(bullet_of_player.lock);



                        if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {
                            if (player1.dead_of_player == 1) {
                                player1.break_show_text_dead_player = 1;
                                lives_back = true;
                            }

                            player1.x_pixel_of_player = SCREEN_WIDTH / 2;
                            player1.y_pixel_of_player = SCREEN_HEIGHT - 50;
                            player1.position_take = 0;
                        }
                        xSemaphoreGive(player1.lock);
                        if (lives_back) {
                            if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                                my_global_values.live = 4;
                            }
                            xSemaphoreGive(my_global_values.lock);
                        }


                        if (positions) {
                            vTaskSuspend(positions);
                        }

                        if (help_to_positions_of_enemy) {
                            vTaskSuspend(help_to_positions_of_enemy);
                        }


                        if (mothership_on_off) {
                            vTaskSuspend(mothership_on_off);
                        }
                        if (mothership_multiplayer) {
                            vTaskSuspend(mothership_multiplayer);
                        }
                        if (control_Multiplayer) {
                            vTaskSuspend(control_Multiplayer);
                        }

                    }
                }
                //GO BACK WITH POUSE

                if (!tumEventGetMouseLeft() && go_back > 0 && time_pressed_pause % 2 == 1) {

                    int resume = 0;
                    go_back = 0;
                    start_game = 0;
                    allow_draw = false;
                    bool lives_back = false;


                    if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                        if (my_global_values.killed_enemies == 40) {
                            if (my_global_values.give_new_values == 1) {
                                my_global_values.give_new_replay = 0;
                                my_global_values.give_new_values = 0;
                                my_global_values.pressed_pause = 0;
                                my_global_values.pressed_replay = 0;
                                printf("BBBBBBBBBBBBBBBBBBB222222222222222222222222222222222222Dooneeee\n");

                                resume = 1;
                            }
                            else {
                                printf("BBBBBBBBBBBBBBBBBBBBBBB22222222222222222222222222222222waaaaaaaaaaaaaaiiiiiiiiiiiit\n");
                                go_back++;
                            }
                        }
                        else {
                            resume = 1;
                            printf("BBBBBBBBBBBBBBBBBBBBBBBBBBBBBB22222222222222222222222222Diiiiiiiiiireeeeeeeeeeeeecttttttt\n");

                        }

                    }
                    xSemaphoreGive(my_global_values.lock);

                    if (resume) {
                        resume = 0;
                        time_pressed_pause = 0;

                        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {

                            my_global_values.level = 0;
                            my_global_values.score = 0;
                            my_global_values.right = 0;
                            my_global_values.left = 1000;
                            my_global_values.five = 10;
                            my_global_values.live = 3;
                            my_global_values.change_position = 0;
                            my_global_values.seconds = 0;
                            my_global_values.y = 0;
                            my_global_values.killed_enemies = 0;
                            my_global_values.speed = 400;
                            my_global_values.game_over = 0;
                        }
                        xSemaphoreGive(my_global_values.lock);










                        if (xSemaphoreTake(mothership_enemy.lock, 0) == pdTRUE)

                        {
                            mothership_enemy.mothership.x_pixel = -20;
                            mothership_enemy.mothership.y_pixel = 2;
                            mothership_enemy.mothership.dead = 0;
                            mothership_enemy.collision_happend = 0;
                            if (mothership_enemy.multiplay_game == true) {
                                mothership_enemy.multiplay_game = false;
                                difficulty = 1;
                                play_multiplay_game = 0;
                                pause_resumed_for_udp = false;
                            }

                        }
                        xSemaphoreGive(mothership_enemy.lock);
                        if (xSemaphoreTake(enemies.lock, 0) == pdTRUE) {
                            for (int i = 0; i < 5; i++) {
                                for (int j = 0; j < 8; j++) {
                                    enemies.enemy_position[i][j].dead = 0;
                                    enemies.enemy_position[i][j].x_pixel = 0;
                                    enemies.enemy_position[i][j].y_pixel = 0;
                                }

                            }
                        }
                        xSemaphoreGive(enemies.lock);
                        if (xSemaphoreTake(green_blocks.lock, 0) == pdTRUE) {
                            for (int i = 0; i < 2; i++) {
                                for (int j = 0; j < 20; j++) {
                                    green_blocks.blocks_blocks[i][j].block_off = 0;
                                }
                            }
                        }
                        xSemaphoreGive(green_blocks.lock);
                        if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {
                            if (bullet_of_enemy.bullet_on == 1 && bullet_of_player.collision_happend == 0) {
                                vTaskResume(enemy_bullet);
                                bullet_of_enemy.collision_happend = 1;
                            }
                            bullet_of_enemy.position_take = 0;



                        }
                        xSemaphoreGive(bullet_of_enemy.lock);

                        if (xSemaphoreTake(bullet_of_player.lock, 0) == pdTRUE) {
                            bullet_of_player.collision_happend = 0;
                            bullet_of_player.bullet_on = 0;
                            bullet_of_player.x_pixel_of_bullet = SCREEN_WIDTH / 2 + 10;
                            bullet_of_player.y_pixel_of_bullet = SCREEN_HEIGHT - 50;
                            bullet_of_player.position_take = 0;

                        }
                        xSemaphoreGive(bullet_of_player.lock);



                        if (xSemaphoreTake(player1.lock, 0) == pdTRUE) {
                            if (player1.dead_of_player == 1) {
                                vTaskResume(show_text_dead_player);
                                player1.break_show_text_dead_player = 1;
                                lives_back = true;
                                printf("Replay after dead from player\n");
                            }
                            player1.x_pixel_of_player = SCREEN_WIDTH / 2;
                            player1.y_pixel_of_player = SCREEN_HEIGHT - 50;
                            player1.position_take = 0;


                        }
                        xSemaphoreGive(player1.lock);



                        if (positions) {
                            vTaskSuspend(positions);

                        }
                        if (help_to_positions_of_enemy) {
                            vTaskSuspend(help_to_positions_of_enemy);
                        }


                        if (mothership_on_off) {
                            vTaskSuspend(mothership_on_off);
                        }
                        if (mothership_multiplayer) {
                            vTaskSuspend(mothership_multiplayer);
                        }

                        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                            if (lives_back) {
                                my_global_values.live = 4;
                            }

                        }
                        xSemaphoreGive(my_global_values.lock);

                    }







                }



                //GAME OVER

                if (game_over == 1) {

                    time_pressed_pause = 1;

                    pause_resumed_for_udp = false;
                    if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                        if (my_global_values.score > my_global_values.highscore && start_game == 1) {
                            my_global_values.highscore = my_global_values.score;
                        }
                        if (my_global_values.score > my_global_values.highscore_multiplayer && play_multiplay_game) {
                            my_global_values.highscore_multiplayer = my_global_values.score;
                        }

                    }
                    xSemaphoreGive(my_global_values.lock);


                    if (time_pressed_pause % 2) {

                        if (move_player_right) {
                            vTaskSuspend(move_player_right);
                        }

                        if (my_Substract) {
                            vTaskSuspend(my_Substract);
                        }

                        if (positions) {
                            vTaskSuspend(positions);
                        }

                        if (help_to_positions_of_enemy) {
                            vTaskSuspend(help_to_positions_of_enemy);
                        }



                        if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
                            if (my_global_values.killed_enemies == 40) {
                                my_global_values.pressed_pause = 1;

                            }

                        }
                        xSemaphoreGive(my_global_values.lock);



                        if (mothership_on_off) {
                            vTaskSuspend(mothership_on_off);
                        }
                        if (mothership) {
                            vTaskSuspend(mothership);

                        }
                        if (mothership_multiplayer) {
                            vTaskSuspend(mothership_multiplayer);
                        }

                        if (xSemaphoreTake(bullet_of_enemy.lock, 0) == pdTRUE) {
                            if (bullet_of_enemy.bullet_on == 1 && bullet_of_enemy.collision_happend == 0) {
                                bullet_of_enemy.collision_happend = 1;
                            }
                            bullet_of_enemy.position_take = 0;

                        }
                        xSemaphoreGive(bullet_of_enemy.lock);


                        if (bullet_of_player_task)
                        {vTaskSuspend(bullet_of_player_task);}


                    }
                }


                xSemaphoreGive(ScreenLock);

            }


        }
        vTaskDelay(1);
    }
}


int main(int argc, char *argv[])
{


    char *bin_folder_path = tumUtilGetBinFolderPath(argv[0]);

    prints("Initializing: ");

    if (tumDrawInit(bin_folder_path)) {
        PRINT_ERROR("Failed to intialize drawing");

    }
    else {
        prints("drawing");
    }

    if (tumEventInit()) {
        PRINT_ERROR("Failed to initialize events");

    }
    else {
        prints(", events");
    }

    if (tumSoundInit(bin_folder_path)) {
        PRINT_ERROR("Failed to initialize audio");

    }
    else {
        prints(", and audio\n");
    }

    if (safePrintInit()) {
        PRINT_ERROR("Failed to init safe print");

    }



    atexit(aIODeinit);
    HandleUDP = xSemaphoreCreateMutex();
    if (!HandleUDP) {
        printf("AAAAAAAAAAAAAAAA\n");
    }

    Movement = xQueueCreate(1, sizeof(opponent_cmd_t));
    if (!Movement) {

    }
    X_player = xQueueCreate(1, sizeof(signed int));
    if (!X_player) {

    }
    Bullet_active = xQueueCreate(1, sizeof(bool));
    if (!Bullet_active) {

    }
    Difficulty = xQueueCreate(1, sizeof(char));
    if (!Difficulty) {

    }
    Pause_Resumed = xQueueCreate(1, sizeof(bool));
    if (!Pause_Resumed) {

    }
    Mothership_UDP = xQueueCreate(1, sizeof(signed int));
    if (!Mothership_UDP) {

    }
    //Load a second font for fun

    bullet_of_player.lock = xSemaphoreCreateMutex();
    if (!bullet_of_player.lock) {
        PRINT_ERROR("Failed to create player's bullet\n");
    }

    buttons.lock = xSemaphoreCreateMutex(); // Locking mechanism
    if (!buttons.lock) {
        PRINT_ERROR("Failed to create buttons lock");

    }
    mothership_enemy.lock = xSemaphoreCreateMutex();
    if (!mothership_enemy.lock) {
        PRINT_ERROR("Failed to create mothership\n");
    }

    DrawSignal = xSemaphoreCreateBinary(); // Screen buffer locking
    if (!DrawSignal) {
        PRINT_ERROR("Failed to create draw signal");

    }

    ScreenLock = xSemaphoreCreateMutex();
    if (!ScreenLock) {
        PRINT_ERROR("Failed to create screen lock");

    }

    green_blocks.lock = xSemaphoreCreateMutex();
    if (!green_blocks.lock) {
        printf("Failed to create greeen blocks\n");
    }

    enemies.lock = xSemaphoreCreateMutex();
    if (!enemies.lock) {
        printf("Failed to create enemies\n");
    }
    player1.lock = xSemaphoreCreateMutex();
    if (!player1.lock) {
        printf("Failed to create Mutex\n");
    }
    bullet_of_enemy.lock = xSemaphoreCreateMutex();
    if (!bullet_of_enemy.lock) {

    }





    // Message sending
    StateQueue = xQueueCreate(STATE_QUEUE_LENGTH, sizeof(unsigned char));
    if (!StateQueue) {
        PRINT_ERROR("Could not open state queue");

    }

    my_global_values.lock = xSemaphoreCreateMutex();
    if (!my_global_values.lock) {
        PRINT_ERROR("Failed to crate my global Values");

    }
    just_for_show_text_dead_player.lock = xSemaphoreCreateMutex();
    if (!just_for_show_text_dead_player.lock) {

    }



    if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE) {
        my_global_values.right = 0;
        my_global_values.left = 1000;
        my_global_values.five = 10;
        my_global_values.live = 3;
        my_global_values.speed = 400;
        printf("KREIERT\n");


    }
    xSemaphoreGive(my_global_values.lock);

    monster1 = tumDrawLoadImage(MONSTER1);
    monster2 = tumDrawLoadImage(MONSTER2);
    monster3 = tumDrawLoadImage(MONSTER3);
    mother = tumDrawLoadImage(MOTHER);






    if (xTaskCreate(Mothership_multiplayer, "Mothership_on_off", mainGENERIC_STACK_SIZE * 2, NULL, configMAX_PRIORITIES - 2, &mothership_multiplayer) != pdPASS) {
        PRINT_ERROR("MOthership_on_off");

    }
    if (xTaskCreate(Mothership_on_off, "Mothership_on_off", mainGENERIC_STACK_SIZE * 2, NULL, configMAX_PRIORITIES - 2, &mothership_on_off) != pdPASS) {
        PRINT_ERROR("MOthership_on_off");

    }
    if (xTaskCreate(Mothership, "Mothership", mainGENERIC_STACK_SIZE * 2, NULL, configMAX_PRIORITIES - 2, &mothership) != pdPASS) {
        PRINT_TASK_ERROR("Mothership");

    }
    if (xTaskCreate(Move_player_right, "Move player right", mainGENERIC_STACK_SIZE * 2, NULL, configMAX_PRIORITIES - 2, &move_player_right) != pdPASS) {
        PRINT_TASK_ERROR("My_Blue_Circle failed");

    }

    if (xTaskCreate(My_Substract, "Move player left", mainGENERIC_STACK_SIZE * 2, NULL, configMAX_PRIORITIES - 2, &my_Substract) != pdPASS) {
        PRINT_TASK_ERROR("My Substact failed ");

    }

    if (xTaskCreate(Enemy_bullet, "Bullet of enemy ", mainGENERIC_STACK_SIZE * 2,
                    NULL, configMAX_PRIORITIES - 2, &enemy_bullet) != pdPASS) {
        PRINT_TASK_ERROR("My_Exercise_2 failed");

    }



    if (xTaskCreate(Show_text_dead_player, "Show text dead player", mainGENERIC_STACK_SIZE * 2,
                    NULL, configMAX_PRIORITIES - 2, &show_text_dead_player) != pdPASS) {
        PRINT_TASK_ERROR("Show text dead player");
    }

    if (xTaskCreate(Show_next_level, "Show text dead player", mainGENERIC_STACK_SIZE * 2,
                    NULL, configMAX_PRIORITIES - 2, &show_next_level) != pdPASS) {
        PRINT_TASK_ERROR("Show text dead player");
    }
    if (xTaskCreate(Bullet_of_player, "Bullet of player", mainGENERIC_STACK_SIZE * 2, NULL, configMAX_PRIORITIES, &bullet_of_player_task) != pdPASS) {
        PRINT_TASK_ERROR("My_Blue_Circle failed");

    }
    if (xTaskCreate(Control_Multiplayer, "Bullet of player", mainGENERIC_STACK_SIZE * 2, NULL, configMAX_PRIORITIES - 2, &control_Multiplayer) != pdPASS) {
        PRINT_TASK_ERROR("My_Blue_Circle failed");

    }



    if (xTaskCreate(Positions, "Positions", mainGENERIC_STACK_SIZE * 2,
                    NULL, configMAX_PRIORITIES - 1, &positions) != pdPASS) {
        PRINT_TASK_ERROR("My_Exercise_2 failed");

    }
    if (xTaskCreate(Help_to_positions_of_enemy, "Help to positions of enemy", mainGENERIC_STACK_SIZE * 2, NULL, configMAX_PRIORITIES - 1, &help_to_positions_of_enemy) != pdPASS) {
        PRINT_TASK_ERROR("My_Blue_Circle failed");

    }



    if (xTaskCreate(Draw_everything, "Draw everything", mainGENERIC_STACK_SIZE * 2,
                    NULL, configMAX_PRIORITIES, &draw_everything) != pdPASS) {
        PRINT_TASK_ERROR("My_Exercise_3 failed");

    }
    if (xTaskCreate(vSwapBuffers, "BufferSwapTask",
                    mainGENERIC_STACK_SIZE * 32, NULL, configMAX_PRIORITIES + 1,
                    BufferSwap) != pdPASS) {
        PRINT_TASK_ERROR("BufferSwapTask");

    }



    tumFUtilPrintTaskStateList();
    vTaskStartScheduler();





}


// cppcheck-suppress unusedFunction
__attribute__((unused)) void vMainQueueSendPassed(void)
{
    /* This is just an example implementation of the "queue send" trace hook. */
}

// cppcheck-suppress unusedFunction
__attribute__((unused)) void vApplicationIdleHook(void)
{
#ifdef GCC_POSIX
    struct timespec xTimeToSleep, xTimeSlept;
    /* Makes the process more agreeable when using the Posix simulator. */
    xTimeToSleep.tv_sec = 1;
    xTimeToSleep.tv_nsec = 0;
    nanosleep(&xTimeToSleep, &xTimeSlept);
#endif
}