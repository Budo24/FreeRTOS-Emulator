#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include <SDL2/SDL_scancode.h>

#include "FreeRTOS.h"
#include "queue.h"
#include "semphr.h"
#include "task.h"
#include "timers.h"

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
#define UDP_BUFFER_SIZE 2000
#define UDP_TEST_PORT_1 1234
#define UDP_TEST_PORT_2 4321
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
static TaskHandle_t StateMachine = NULL;
static TaskHandle_t BufferSwap = NULL;
static TaskHandle_t my_Exercise_2 = NULL;
static TaskHandle_t my_Exercise_3 = NULL;
static TaskHandle_t my_Red_Circle = NULL;
static TaskHandle_t my_Blue_Circle = NULL;
static TaskHandle_t Seconds = NULL;
static TaskHandle_t TaskBinarySemaphoreTakeButton = NULL;
static TaskHandle_t TaskTakeNotify = NULL;
 TaskHandle_t my_task_1 = NULL;
 TaskHandle_t my_task_2 = NULL;
 TaskHandle_t my_task_3 = NULL;
 TaskHandle_t my_task_4 = NULL;
 TaskHandle_t my_Exercise_4= NULL;
 TaskHandle_t value = NULL;
SemaphoreHandle_t my_wake_up_3 = NULL;

static SemaphoreHandle_t my_LockOutput = NULL;
static SemaphoreHandle_t my_LockIndex = NULL;
char output[15][25] = {
    {" 1 : "},
    {" 2 : "},
    {" 3 : "},
    {" 4 : "},
    {" 5 : "},
    {" 6 : "},
    {" 7 : "},
    {" 8 : "},
    {" 9 : "},
    {" 10 : "},
    {" 11 : "},
    {" 12 : "},
    {" 13 : "},
    {" 14 : "},
    {" 15 : "},   
};
int m = 0;




static TimerHandle_t auto_reload_f_g_timer = NULL;
static QueueHandle_t StateQueue = NULL;

static SemaphoreHandle_t DrawSignal = NULL;
static SemaphoreHandle_t ScreenLock = NULL;
static SemaphoreHandle_t Button_F = NULL;

//Hier are all global variables, locked in mutex(in main)

typedef struct my_values{
     int turn_on_blue_circle;
     int turn_on_red_circle;
     int seconds;
     int pressed_f;
     int pressed_g;
     int times_pressed_f;
     int times_pressed_g;
     int task_semaphore;
     int task_notify;
    SemaphoreHandle_t lock;
} my_values_t;

static my_values_t my_global_values = { 0 };

//Used just few times
static my_values_t my_global_just_for_my_exercise_3 = { 0 };

//

typedef struct buttons_buffer {
    unsigned char buttons[SDL_NUM_SCANCODES];
    SemaphoreHandle_t lock;
} buttons_buffer_t;

static buttons_buffer_t buttons = { 0 };



void vApplicationGetIdleTaskMemory( StaticTask_t **ppxIdleTaskTCBBuffer,
                                    StackType_t **ppxIdleTaskStackBuffer,
                                    uint32_t *pulIdleTaskStackSize )
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
void vApplicationGetTimerTaskMemory( StaticTask_t **ppxTimerTaskTCBBuffer,
                                     StackType_t **ppxTimerTaskStackBuffer,
                                     uint32_t *pulTimerTaskStackSize )
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

static int vCheckStateInput(void)
{
    if (xSemaphoreTake(buttons.lock, 0) == pdTRUE) {
        if (buttons.buttons[KEYCODE(E)]) {
            buttons.buttons[KEYCODE(E)] = 0;
            if (StateQueue) {
                xSemaphoreGive(buttons.lock);
                xQueueSend(StateQueue, &next_state_signal, 0);
                return 0;
            }
            return -1;
        }
        xSemaphoreGive(buttons.lock);
    }

    return 0;
}
/*
 * Changes the state, either forwards of backwards
 */
void changeState(volatile unsigned char *state, unsigned char forwards)
{
    switch (forwards) {
        case NEXT_TASK:
            if (*state == STATE_COUNT - 1) {
                *state = 0;
            }
            else {
                (*state)++;
            }
            break;
        case PREV_TASK:
            if (*state == 0) {
                *state = STATE_COUNT - 1;
            }
            else {
                (*state)--;
            }
            break;
        default:
            break;
    }
}

/*
 * Example basic state machine with sequential states
 */
void basicSequentialStateMachine(void *pvParameters)
{
    unsigned char current_state = STARTING_STATE; // Default state
    unsigned char state_changed =
        1; // Only re-evaluate state if it has changed
    unsigned char input = 0;

    const int state_change_period = STATE_DEBOUNCE_DELAY;

    TickType_t last_change = xTaskGetTickCount();

    while (1) {
        if (state_changed) {
            goto initial_state;
        }

        // Handle state machine input
        if (StateQueue)
            if (xQueueReceive(StateQueue, &input, portMAX_DELAY) ==
                pdTRUE)
                if (xTaskGetTickCount() - last_change >
                    state_change_period) {
                    changeState(&current_state, input);
                    state_changed = 1;
                    last_change = xTaskGetTickCount();
                }

initial_state:
        // Handle current state
        if (state_changed) {
            switch (current_state) {
                case STATE_ONE:
                   
                    if (my_Exercise_3) {
                        vTaskSuspend(my_Exercise_3);
                    }
                   
                     if (my_Exercise_2) {
                        vTaskResume(my_Exercise_2);
                    }
                     if(my_Exercise_4)
                    {
                        vTaskSuspend(my_Exercise_4);
                    }
                    if(my_Red_Circle)
                    {
                        vTaskSuspend(my_Red_Circle);
                        
                    }
                    if(my_Blue_Circle)
                    {
                        vTaskSuspend(my_Blue_Circle);
                    }

                    
                    
                    break;
                case STATE_TWO:
                      if(my_Exercise_2) {
                        vTaskSuspend(my_Exercise_2);
                    }
                    if (my_Exercise_3) {
                        vTaskResume(my_Exercise_3);
                    }
                   
                    if(my_Exercise_4)
                    {
                        vTaskSuspend(my_Exercise_4);
                    }
                    if(my_Red_Circle)
                    {
                        vTaskResume(my_Red_Circle);
                    }
                    if(my_Blue_Circle)
                    {
                        vTaskResume(my_Blue_Circle);
                    }
                    
                       
                  
                  
                    break;
                case STATE_THREE:
                  if (my_Exercise_2) {
                        vTaskSuspend(my_Exercise_2);
                    }
                    if (my_Exercise_3) {
                        vTaskSuspend(my_Exercise_3);
                    }
                    if(my_Exercise_4)
                    {
                        vTaskResume(my_Exercise_4);
                    }
                    if(my_Red_Circle)
                    {
                        vTaskSuspend(my_Red_Circle);
                    }
                    if(my_Blue_Circle)
                    {
                        vTaskSuspend(my_Blue_Circle);
                    }
                    
                
                 default:
                    break;
            }
            state_changed = 0;
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

//Now coming all function, which were used for exercise 2

void my_Rotation(int *degree_my, float *radians_my, float *x_coor_my, float *y_coor_my)
{
      
    //Circle is done, do from begin

    if(*degree_my>360)
    {
    *degree_my=0;
    }
    
    //convert to radians
    
    *radians_my=(*degree_my*PI)/180;

    //use trigonometric 
    *x_coor_my=cos(*radians_my)*radius1;
    *y_coor_my=sin(*radians_my)*radius1;



    tumDrawCircle(coordinate_origin-*x_coor_my+tumEventGetMouseX()-200,SCREEN_HEIGHT/2-*y_coor_my+tumEventGetMouseY()-200,30,Red);
    tumDrawFilledBox(coordinate_origin+*x_coor_my+tumEventGetMouseX()-200,(SCREEN_HEIGHT)/2+*y_coor_my+tumEventGetMouseY()-200,40,40,Blue);

    *degree_my = *degree_my+1;  
         
}

void my_Triangle()
{
                coord_t coordinates_triangle[3];
                coordinates_triangle[0].x=coordinate_origin-50+tumEventGetMouseX()-200;
                coordinates_triangle[0].y=SCREEN_HEIGHT/2+tumEventGetMouseY()-200;
                coordinates_triangle[1].x=coordinate_origin+50+tumEventGetMouseX()-200;
                coordinates_triangle[1].y=SCREEN_HEIGHT/2+tumEventGetMouseY()-200;
                coordinates_triangle[2].x=coordinate_origin+tumEventGetMouseX()-200;
                coordinates_triangle[2].y=SCREEN_HEIGHT/2+50+tumEventGetMouseY()-200;
                tumDrawTriangle(&coordinates_triangle[0],Yellow);
}

void my_text_should_move(int *text_width_my)
{
                tumDrawText("This text should move",-150+*text_width_my, 0, Black);

                if(*text_width_my>SCREEN_WIDTH+150)
                {
                *text_width_my=0;
                }
                *text_width_my = *text_width_my+1;
}

void my_buttons(int *pressed_a, int *pressed_b, int *pressed_c,  int *pressed_d, int *times_pressed_a, int *times_pressed_b, int *times_pressed_c, int *times_pressed_d)
{  

static char str1[100] = { 0 };

if (xSemaphoreTake(buttons.lock, 0) == pdTRUE) 
{

sprintf(str1, "A: %d | B: %d | C: %d | D: %d",
buttons.buttons[KEYCODE(A)],
buttons.buttons[KEYCODE(B)],
buttons.buttons[KEYCODE(C)],
buttons.buttons[KEYCODE(D)]);

                
                
checkDraw(tumDrawText(str1, 10+tumEventGetMouseX()-200, DEFAULT_FONT_SIZE * 2+tumEventGetMouseY()-200, Black),
               __FUNCTION__);
}
        
//Letter A

//Pressed_A

if(buttons.buttons[KEYCODE(A)])
{
*pressed_a=*pressed_a +1;
}

//Not_pressed_A
if(!buttons.buttons[KEYCODE(A)])
{ 
if (*pressed_a>0)
{
*times_pressed_a=*times_pressed_a+1;
}

 *pressed_a=0;

}
sprintf(str1, "A is pressed so many times: %d", *times_pressed_a);
checkDraw(tumDrawText(str1, 10+tumEventGetMouseX()-200, DEFAULT_FONT_SIZE * 4+tumEventGetMouseY()-200, Black),
                          __FUNCTION__);

                   
//Letter B

//Pressed_B

if(buttons.buttons[KEYCODE(B)])
{
*pressed_b = *pressed_b +1;
}

//Not_pressed_B

if(!buttons.buttons[KEYCODE(B)])
{ 
if (*pressed_b>0)
{
*times_pressed_b=*times_pressed_b+1;
}
*pressed_b=0;
}
sprintf(str1, "B is pressed so many times: %d", *times_pressed_b);
checkDraw(tumDrawText(str1, 10+tumEventGetMouseX()-200, DEFAULT_FONT_SIZE * 6+tumEventGetMouseY()-200, Black),
                           __FUNCTION__);

//Letter C

//Pressed_C
if(buttons.buttons[KEYCODE(C)])
{
*pressed_c=*pressed_c+1;
}

//Not_pressed_C

if(!buttons.buttons[KEYCODE(C)])
{ 
if (*pressed_c>0)
{
*times_pressed_c=*times_pressed_c+1;
}
*pressed_c=0;
}
sprintf(str1, "C is pressed so many times: %d", *times_pressed_c);
checkDraw(tumDrawText(str1, 10+tumEventGetMouseX()-200, DEFAULT_FONT_SIZE * 8+tumEventGetMouseY()-200, Black),
               __FUNCTION__);

//Letter D

//Pressed_D

if(buttons.buttons[KEYCODE(D)])
{
*pressed_d=*pressed_d+1;
}
//Not_pressed_D

if(!buttons.buttons[KEYCODE(D)])
{ 
if (*pressed_d>0)
{
*times_pressed_d=*times_pressed_d+1;
}
*pressed_d=0;
}
sprintf(str1, "D is pressed so many times: %d", *times_pressed_d);
checkDraw(tumDrawText(str1, 10+tumEventGetMouseX()-200, DEFAULT_FONT_SIZE * 10+tumEventGetMouseY()-200, Black),
            __FUNCTION__);
sprintf(str1,"Press left mouse button , if you want to reset times pressure of every letter");
checkDraw(tumDrawText(str1, 10+tumEventGetMouseX()-200, DEFAULT_FONT_SIZE * 12+tumEventGetMouseY()-200, Black),
                 __FUNCTION__);

                 
xSemaphoreGive(buttons.lock);
}

void my_Reset_A_B_C_D(unsigned char reset, int *times_pressed_a, int *times_pressed_b, int *times_pressed_c, int *times_pressed_d)
{
  if(reset)
  {
    *times_pressed_a=0;
    *times_pressed_b=0;
    *times_pressed_c=0;
    *times_pressed_d=0;
  }

}

void my_DrawMouse()
{
    static char str[100] = { 0 };
    sprintf(str, "Axis 1: %5d | Axis 2: %5d", tumEventGetMouseX(),tumEventGetMouseY());
    checkDraw(tumDrawText(str, 10+tumEventGetMouseX()-200, DEFAULT_FONT_SIZE * 0.5+tumEventGetMouseY()-200, Black),
           __FUNCTION__);
}

void my_down_text()
{
        tumDrawText("AVDIC SABAHUDIN",0+tumEventGetMouseX() , SCREEN_HEIGHT-250+tumEventGetMouseY(), Red);
}


void My_Exercise_2(void *pvParameters)
{

    //Local  variable, which was later in functions changed

    int degree=0;
    float radians=0;
    float   x_coor=0;
    float  y_coor=0;
    int   text_width = 0;
    int pressed_a=0;
    int pressed_b=0;
    int pressed_c=0;
    int pressed_d=0;
    int times_pressed_a=0;
    int times_pressed_b=0;
    int times_pressed_c=0;
    int times_pressed_d=0;


    while (1) {
        if (DrawSignal)
            if (xSemaphoreTake(DrawSignal, portMAX_DELAY) ==
                pdTRUE) {
                tumEventFetchEvents(FETCH_EVENT_BLOCK |
                                    FETCH_EVENT_NO_GL_CHECK);
                xGetButtonInput(); // Update global input

                xSemaphoreTake(ScreenLock, portMAX_DELAY);

                // Clear screen
                 checkDraw(tumDrawClear(White),  __FUNCTION__);

                
                 my_Rotation(&degree, &radians, &x_coor, &y_coor);

                 my_Triangle();

                 my_text_should_move(&text_width);

                 my_buttons(&pressed_a, &pressed_b, &pressed_c, &pressed_d, &times_pressed_a, &times_pressed_b, &times_pressed_c, &times_pressed_d);
                 
                 my_Reset_A_B_C_D(tumEventGetMouseLeft(), &times_pressed_a, &times_pressed_b, &times_pressed_c, &times_pressed_d);

                 my_DrawMouse();

                 my_down_text();


                 xSemaphoreGive(ScreenLock);
              
                // Get input and check for state change

                vCheckStateInput();
            }
    }
}



//Here are all functions which are required for exercise 3

void vTaskBinarySemaphoreTakeButton(void *pvParameters)
{
    
    while(1)
    {
        
        if(xSemaphoreTake(Button_F, portMAX_DELAY))
         {
            
               if(xSemaphoreTake(my_global_values.lock,0)==pdTRUE)
               {
                   my_global_values.pressed_f++;
               }
               xSemaphoreGive(my_global_values.lock);       
         }   
    } 

}

void vTaskTakeNotify(void *pvParameters)
{
    uint32_t notificationValue=0;
    while(1)
    {

        notificationValue = ulTaskNotifyTake(pdTRUE,portMAX_DELAY);

        if(notificationValue>0)
        {  
            
              if(xSemaphoreTake(my_global_values.lock,0)==pdTRUE)
              {
                   my_global_values.pressed_g++;
              }
             xSemaphoreGive(my_global_values.lock);

        }
    }
}

void My_Seconds(void *pvParameters)
{
    TickType_t xLast;
    const TickType_t xFrequency = 1000 / portTICK_PERIOD_MS;
    // Initialise the xLastWakeTime variable with the current time.
   
    while (1) {
                      xLast = xTaskGetTickCount();

                     if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE)
                           {
                               
                                 my_global_values.seconds++;     
                           }
                           xSemaphoreGive(my_global_values.lock);
                          vTaskDelayUntil( &xLast,xFrequency);
                       }            
}

void my_draw_circles()
{
    if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE)
                {

                    if(my_global_values.turn_on_red_circle==1)
                    tumDrawCircle(100,100,50,Red);

                    if(my_global_values.turn_on_blue_circle==1)
                    tumDrawCircle(210,100,50,Blue);

                }
                 xSemaphoreGive(my_global_values.lock);
}
void my_draw_time_and_options_for_button()
{
    static char str1[100];
     if(xSemaphoreTake(my_global_values.lock,0)==pdTRUE)

                          { 
                        sprintf(str1, "Time in Seconds[J Start/Stop]: %d             Press [F] or [G]", my_global_values.seconds);
                        xSemaphoreGive(my_global_values.lock);
                            checkDraw(tumDrawText(str1, 10, DEFAULT_FONT_SIZE * 14, Black),
                          __FUNCTION__);

                           }

                           xSemaphoreGive(my_global_values.lock);

}

void my_control_time(int *pressed_j, int *times_pressed_j)
{
    if(xSemaphoreTake(buttons.lock,0)==pdTRUE)
       {
            if(buttons.buttons[KEYCODE(J)])
                {
                *pressed_j=*pressed_j+1;
                }
                if(!buttons.buttons[KEYCODE(J)])
                {
                if(*pressed_j>0)
                {
                *times_pressed_j=*times_pressed_j+1;
                }
                *pressed_j=0;
                }
                }
    xSemaphoreGive(buttons.lock);

    if(*times_pressed_j%2==0)
    {
    if(Seconds)
    {
    vTaskResume(Seconds);}
    }
    


    if(*times_pressed_j%2!=0)
    {
    if(Seconds)
    {  
    vTaskSuspend(Seconds);}
    }
}

void my_button_f_or_button_g_triggered(int *BUTTON_f, int *BUTTON_g)
{
      if(*BUTTON_f==0 || *BUTTON_g==0)
                     {
                     if(xSemaphoreTake(buttons.lock,0)==pdTRUE)
                     {

                     if(buttons.buttons[KEYCODE(F)])
                     {
                         *BUTTON_f=1;
                         if(xSemaphoreTake(my_global_just_for_my_exercise_3.lock,0)==pdTRUE)
                         my_global_just_for_my_exercise_3.task_semaphore=1;
                         xSemaphoreGive(my_global_just_for_my_exercise_3.lock);
                     }
                     if(buttons.buttons[KEYCODE(G)])
                     {
                         *BUTTON_g=1;
                         if(xSemaphoreTake(my_global_just_for_my_exercise_3.lock,0)==pdTRUE)
                         my_global_just_for_my_exercise_3.task_notify=1;
                         xSemaphoreGive(my_global_just_for_my_exercise_3.lock);
                     }
                     }

                     xSemaphoreGive(buttons.lock);
                    }


}


void my_button_f()
{
 static char str1[100] = { 0 };

 if(xSemaphoreTake(my_global_just_for_my_exercise_3.lock,0)==pdTRUE)
    {
     if(my_global_just_for_my_exercise_3.task_semaphore==1)
        {
          if(xSemaphoreTake(buttons.lock,0)==pdTRUE)
              {

                if(buttons.buttons[KEYCODE(F)])
                  {
                       xSemaphoreGive(Button_F);
                  }
                       sprintf(str1, "F: %d", buttons.buttons[KEYCODE(F)]);          
                       checkDraw(tumDrawText(str1, 10, DEFAULT_FONT_SIZE * 16, Black), __FUNCTION__);
               
                if(!buttons.buttons[KEYCODE(F)])
                 {
                       if(xSemaphoreTake(my_global_values.lock,0)==pdTRUE)
                       { 
                         if(my_global_values.pressed_f>0)
                         {
                            my_global_values.times_pressed_f++;
                            my_global_values.pressed_f=0;
                         }

                        }

                        xSemaphoreGive(my_global_values.lock);
                      
                 }
                        xSemaphoreGive(buttons.lock);

                if(xSemaphoreTake(my_global_values.lock,0)==pdTRUE)
                sprintf(str1, "F is pressed so many times: %d", my_global_values.times_pressed_f);
                xSemaphoreGive(my_global_values.lock);
                checkDraw(tumDrawText(str1, 10, DEFAULT_FONT_SIZE * 18, Black),
                          __FUNCTION__);
             }     
        }   
    }
                        xSemaphoreGive(my_global_just_for_my_exercise_3.lock);
}  

void my_button_g()
{
 static char str1[100] = { 0 };

 if(xSemaphoreTake(my_global_just_for_my_exercise_3.lock,0)==pdTRUE)
    {
     if(my_global_just_for_my_exercise_3.task_notify==1)
        {
          if(xSemaphoreTake(buttons.lock,0)==pdTRUE)
              {

                if(buttons.buttons[KEYCODE(G)])
                  {
                       xTaskNotifyGive(TaskTakeNotify);
                  }
                       sprintf(str1, "G: %d", buttons.buttons[KEYCODE(G)]);          
                       checkDraw(tumDrawText(str1, 10, DEFAULT_FONT_SIZE * 20, Black), __FUNCTION__);
               
                if(!buttons.buttons[KEYCODE(G)])
                 {
                       if(xSemaphoreTake(my_global_values.lock,0)==pdTRUE)
                       { 
                         if(my_global_values.pressed_g>0)
                         {
                            my_global_values.times_pressed_g++;
                            my_global_values.pressed_g=0;
                         }

                        }

                        xSemaphoreGive(my_global_values.lock);
                      
                 }
                        xSemaphoreGive(buttons.lock);

                if(xSemaphoreTake(my_global_values.lock,0)==pdTRUE)
                sprintf(str1, "G is pressed so many times: %d", my_global_values.times_pressed_g);
                xSemaphoreGive(my_global_values.lock);
                checkDraw(tumDrawText(str1, 10, DEFAULT_FONT_SIZE * 22, Black),
                          __FUNCTION__);
             }     
        }   
    }
                        xSemaphoreGive(my_global_just_for_my_exercise_3.lock);
}   

void myTimerCallBack(TimerHandle_t xTimer)
{
     if(( uint32_t ) pvTimerGetTimerID( xTimer ))
     {
         if(xSemaphoreTake(my_global_values.lock,0)==pdTRUE)
         {
             my_global_values.times_pressed_f=0;
             my_global_values.times_pressed_g=0;
         }
         xSemaphoreGive(my_global_values.lock);
     } 
    
}

void My_Red_Circle(void *pyParameters)
{
    TickType_t xLastWakeTime;
    const TickType_t xFrequency = 500 / portTICK_PERIOD_MS;
    // Initialise the xLastWakeTime variable with the current time.
    xLastWakeTime = xTaskGetTickCount();
   
      

    while (1) {
               
                if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE)
                       {
                           if(my_global_values.turn_on_red_circle==0)
                           {
                                 my_global_values.turn_on_red_circle++;
                           }
                          else
                          {
                                 my_global_values.turn_on_red_circle--; 
                          }
                                 xSemaphoreGive(my_global_values.lock);
                       }

                vTaskDelayUntil( &xLastWakeTime,xFrequency); 
            
}
}

void My_Blue_Circle(void *pvParameters)
{
    TickType_t xLastWakeTime;
    const TickType_t xFrequency = 250 / portTICK_PERIOD_MS;
    // Initialise the xLastWakeTime variable with the current time.
    xLastWakeTime = xTaskGetTickCount();
     
    while (1) {
                     if (xSemaphoreTake(my_global_values.lock, 0) == pdTRUE)
                       {
                           if(my_global_values.turn_on_blue_circle==0)
                           {
                                 my_global_values.turn_on_blue_circle++;
                           }

                          else
                          {
                                 my_global_values.turn_on_blue_circle--; 
                          }
                                 xSemaphoreGive(my_global_values.lock);
                       }
                    
                vTaskDelayUntil( &xLastWakeTime,xFrequency);
            }
}


void My_Exercise_3(void *pvParameters)
{
    int pressed_j = 0;
    int times_pressed_j = 0;
    int BUTTON_f=0;
    int BUTTON_g=0;

    while (1) {


        if (DrawSignal)
            if (xSemaphoreTake(DrawSignal, portMAX_DELAY) ==
                pdTRUE) {
                tumEventFetchEvents(FETCH_EVENT_BLOCK |
                                    FETCH_EVENT_NO_GL_CHECK);
                xGetButtonInput(); // Update global button data

                xSemaphoreTake(ScreenLock, portMAX_DELAY);
                // Clear screen
                checkDraw(tumDrawClear(White),  __FUNCTION__);

                my_draw_circles();

                my_draw_time_and_options_for_button();

                my_control_time(&pressed_j, &times_pressed_j);

                my_button_f_or_button_g_triggered(&BUTTON_f, &BUTTON_g);

                my_button_f();

                my_button_g();

                }
                xSemaphoreGive(ScreenLock);
                vCheckStateInput();

                }
               
                
    }
       
//Here is exercise 4

void My_task_1(void * pvParameters){
    char send = '1';
    int counter = 1;
    TickType_t LastWakeTime;
    LastWakeTime = xTaskGetTickCount();
    while(1){
        if(counter % 4 == 0)
        vTaskResume(my_task_4);
        if(counter % 2 == 0) vTaskResume(my_task_2);
        if(xSemaphoreTake(my_wake_up_3, 0) == pdTRUE){
            vTaskResume(my_task_3);
        }
        if(xSemaphoreTake(my_LockOutput, 0) == pdTRUE){
            strncat(output[m], &send, 1);
            xSemaphoreGive(my_LockOutput);
        }
        if(xSemaphoreTake(my_LockIndex, 0 ) == pdTRUE){
            m++;
            xSemaphoreGive(my_LockIndex);
        }
        counter++;
        if(counter == 16) {
            vTaskSuspend(NULL);
        }
        vTaskDelayUntil(&LastWakeTime,(TickType_t )1);
        LastWakeTime = xTaskGetTickCount();
        
    }
}

void My_task_2(void * pvParameters){
    char send = '2';
    vTaskSuspend(NULL);
    while(1){
        
        if(xSemaphoreTake(my_LockOutput, 0) == pdTRUE){
            strncat(output[m], &send, 1);
            xSemaphoreGive(my_LockOutput);
        }
        xSemaphoreGive(my_wake_up_3);
        
        
        vTaskSuspend(NULL);
        
    }
}

void My_task_3(void * pvParameters){
    char send = '3';
    vTaskSuspend(NULL);
    while(1){
        if(xSemaphoreTake(my_LockOutput, 0) == pdTRUE){
            strncat(output[m], &send, 1);
            xSemaphoreGive(my_LockOutput);
        }
        vTaskSuspend(NULL);
       
    }
}



void My_task_4(void * pvParameters){
    
    char send = '4';
    vTaskSuspend(NULL);
    while(1){
        if(xSemaphoreTake(my_LockOutput, 0) == pdTRUE){
            strncat(output[m], &send, 1);
            xSemaphoreGive(my_LockOutput);
        }
        vTaskSuspend(NULL);
         
    }
    

}



void My_Exercise_4(void * pvParameters){
    
    signed short x = SCREEN_WIDTH/2 - 100;
    signed short y = SCREEN_HEIGHT/2 - 100;
    TickType_t xLastTick = 1;
    while(1){
        if(DrawSignal){
            if(xSemaphoreTake(DrawSignal, portMAX_DELAY) == pdTRUE){
                xSemaphoreTake(ScreenLock, portMAX_DELAY);

                   xGetButtonInput(); 
                
                checkDraw(tumDrawClear(White), __FUNCTION__);
                
                checkDraw(tumDrawText(output[0], x, y,  Black), __FUNCTION__);
                checkDraw(tumDrawText(output[1], x, y + 20, Black), __FUNCTION__);
                checkDraw(tumDrawText(output[2], x, y + 40, Black), __FUNCTION__);
                checkDraw(tumDrawText(output[3], x, y + 60, Black),__FUNCTION__);
                checkDraw(tumDrawText(output[4], x, y + 80, Black),__FUNCTION__); 
                checkDraw(tumDrawText(output[5], x, y + 100, Black), __FUNCTION__);
                checkDraw(tumDrawText(output[6], x, y + 120, Black),  __FUNCTION__);
                checkDraw(tumDrawText(output[7], x, y + 140, Black), __FUNCTION__);
                checkDraw(tumDrawText(output[8], x, y + 160, Black), __FUNCTION__);
                checkDraw(tumDrawText(output[9], x, y + 180, Black),  __FUNCTION__);
                checkDraw(tumDrawText(output[10], x, y + 200, Black), __FUNCTION__);
                checkDraw(tumDrawText(output[11], x, y + 220, Black),  __FUNCTION__);
                checkDraw(tumDrawText(output[12], x, y + 240, Black),  __FUNCTION__);
                checkDraw(tumDrawText(output[13], x, y + 260, Black),  __FUNCTION__);
                checkDraw(tumDrawText(output[14], x, y + 280, Black),  __FUNCTION__);
            
                xSemaphoreGive(ScreenLock);
                        
            }
            
        }

        vCheckStateInput();
        vTaskDelayUntil(&xLastTick,(TickType_t)1);
        
    }
    
}

int main(int argc, char *argv[])
{
   
  char *bin_folder_path = tumUtilGetBinFolderPath(argv[0]);

    prints("Initializing: ");

    if (tumDrawInit(bin_folder_path)) {
        PRINT_ERROR("Failed to intialize drawing");
        goto err_init_drawing;
    }
    else {
        prints("drawing");
    }

    if (tumEventInit()) {
        PRINT_ERROR("Failed to initialize events");
        goto err_init_events;
    }
    else {
        prints(", events");
    }

    if (tumSoundInit(bin_folder_path)) {
        PRINT_ERROR("Failed to initialize audio");
        goto err_init_audio;
    }
    else {
        prints(", and audio\n");
    }

    if (safePrintInit()) {
        PRINT_ERROR("Failed to init safe print");
        goto err_init_safe_print;
    }

   

    atexit(aIODeinit);

    //Load a second font for fun
    tumFontLoadFont(FPS_FONT, DEFAULT_FONT_SIZE);

    buttons.lock = xSemaphoreCreateMutex(); // Locking mechanism
    if (!buttons.lock) {
        PRINT_ERROR("Failed to create buttons lock");
        goto err_buttons_lock;
    }
    Button_F = xSemaphoreCreateBinary();
    if(!Button_F) {
        PRINT_ERROR("Failed to create Binary Semaphore");
        goto err_binary_semaphore;
    }

    DrawSignal = xSemaphoreCreateBinary(); // Screen buffer locking
    if (!DrawSignal) {
        PRINT_ERROR("Failed to create draw signal");
        goto err_draw_signal;
    }
    ScreenLock = xSemaphoreCreateMutex();
    if (!ScreenLock) {
        PRINT_ERROR("Failed to create screen lock");
        goto err_screen_lock;
    }
  
    my_LockIndex = xSemaphoreCreateMutex();
    if(!my_LockIndex){
        PRINT_ERROR("Failed to create index lock");
        goto err_my_LockIndex;
    
    }
    my_LockOutput = xSemaphoreCreateMutex();
    if(!my_LockOutput){
        PRINT_ERROR("Failed to create output lock");
        goto err_my_LockOutput;
       
    }
    my_wake_up_3= xSemaphoreCreateBinary();
    if(!my_wake_up_3){
        PRINT_ERROR("Failed to create binary semaphore for waking the third task in exercise 4");
        goto err_my_wake_up_3;

    }

    // Message sending
    StateQueue = xQueueCreate(STATE_QUEUE_LENGTH, sizeof(unsigned char));
    if (!StateQueue) {
        PRINT_ERROR("Could not open state queue");
        goto err_state_queue;
    }

    my_global_values.lock = xSemaphoreCreateMutex();
    if(!my_global_values.lock)
    {
        PRINT_ERROR("Failed to crate my global Values");
        goto err_my_global_values;
    } 

    my_global_just_for_my_exercise_3.lock = xSemaphoreCreateMutex();
    if(!my_global_just_for_my_exercise_3.lock)
    {
        PRINT_ERROR("Failed to crate my global Values for exercise 3");
        goto err_my_global_just_for_my_exercise_3;

    }

     auto_reload_f_g_timer = xTimerCreate("auto_reload_f_g_timer", 15000 /portTICK_RATE_MS, pdTRUE, (void*) 1 , myTimerCallBack);

     

    if (xTaskCreate(basicSequentialStateMachine, "StateMachine",
                    mainGENERIC_STACK_SIZE * 2, NULL,
                    configMAX_PRIORITIES - 1, StateMachine) != pdPASS) {
        PRINT_TASK_ERROR("StateMachine");
        goto err_statemachine;
    }

    if (xTaskCreate(vSwapBuffers, "BufferSwapTask",
                    mainGENERIC_STACK_SIZE * 2, NULL, configMAX_PRIORITIES,
                    BufferSwap) != pdPASS) {
        PRINT_TASK_ERROR("BufferSwapTask");
        goto err_bufferswap;
    }

    /** Demo Tasks */
    if (xTaskCreate(My_Exercise_2, "My_Exercise_2 ", mainGENERIC_STACK_SIZE * 2,
                    NULL, mainGENERIC_PRIORITY, &my_Exercise_2) != pdPASS) {
        PRINT_TASK_ERROR("My_Exercise_2 failed");
        goto err_My_Exercise_2;
    }
    if (xTaskCreate(My_Exercise_3, "My_Exercise_3", mainGENERIC_STACK_SIZE * 2,
                    NULL, mainGENERIC_PRIORITY, &my_Exercise_3) != pdPASS) {
        PRINT_TASK_ERROR("My_Exercise_3 failed");
        goto err_My_Exercise_3;
    }
    if (xTaskCreate(My_Red_Circle, "My_Red_Circle", mainGENERIC_STACK_SIZE *2 ,
                    NULL,1, &my_Red_Circle) != pdPASS) {
        PRINT_TASK_ERROR("My_Red_Circle failed");
        goto err_My_Red_Circle;
    }
    if(xTaskCreate(My_Blue_Circle, "My_Blue_Circle", mainGENERIC_STACK_SIZE *2 ,NULL,2, &my_Blue_Circle)!=pdPASS)
    {
        PRINT_TASK_ERROR("My_Blue_Circle failed");
        goto err_my_Blue_Circle;
    } 
    if (xTaskCreate(My_Seconds, "My_Seconds", mainGENERIC_STACK_SIZE *2 ,
                    NULL, mainGENERIC_PRIORITY, &Seconds) != pdPASS) {

                         PRINT_TASK_ERROR("Seconds failed");
        goto err_My_Seconds;
    }
   


  
    if (xTaskCreate(vTaskBinarySemaphoreTakeButton, "TaskBinarySemaphoreTakeButton", mainGENERIC_STACK_SIZE *2 ,
                    NULL, 4, &TaskBinarySemaphoreTakeButton) != pdPASS) {
        PRINT_TASK_ERROR("TaskBinarySemaphoreTakeButton failed");
        goto err_task_binary_semaphore_take_button;
    } 
    if (xTaskCreate(vTaskTakeNotify, "TaskTakeNotify", mainGENERIC_STACK_SIZE *2 ,
                    NULL, 3, &TaskTakeNotify) != pdPASS) {
        PRINT_TASK_ERROR("TaskTakeNotify failed");
        goto err_TaskTakeNotify;
    }      
     if(xTaskCreate(My_task_1, "task1", mainGENERIC_STACK_SIZE, NULL, 1, &my_task_1) != pdTRUE){
        PRINT_TASK_ERROR("Could not start task for printing 1");
        goto err_My_task_1;
     
    }
    
    if(xTaskCreate(My_task_2, "task2", mainGENERIC_STACK_SIZE, NULL, 2, &my_task_2) != pdTRUE){
        PRINT_TASK_ERROR("Could not start task for printing 2");
        goto err_My_task_2;
       
    }
    
    if(xTaskCreate(My_task_3, "task3", mainGENERIC_STACK_SIZE, NULL, 3, &my_task_3) != pdTRUE){
        PRINT_TASK_ERROR("Could not start task for printing 3");
        goto err_My_task_3;

       
    }
    
    if(xTaskCreate(My_task_4, "task4", mainGENERIC_STACK_SIZE, NULL, 4, &my_task_4) != pdTRUE){
        PRINT_TASK_ERROR("Could not start task for printing 4");
        goto err_My_task_4;
       
    }

    if(xTaskCreate(My_Exercise_4, "printElements", mainGENERIC_STACK_SIZE, NULL, mainGENERIC_PRIORITY, &my_Exercise_4) != pdTRUE){
        PRINT_TASK_ERROR("Could not start task for printing elements in the 4th exercise");
        goto err_My_Exercise_4;
        
    }
    
    
    tumFUtilPrintTaskStateList();
    if( auto_reload_f_g_timer == NULL )
    {
    printf("TIMER WAS NOT CREATED\n");
    }
    else
    {
    if( xTimerStart( auto_reload_f_g_timer, 0 ) != pdPASS )
    {
    printf("TIMER COULD NOT BE SET INTO ACTIVE STATE\n");
    }
    else
    {
    printf("EVERYTHING IS FINE\n");
    }
    }

    vTaskSuspend(my_Exercise_2);
    vTaskSuspend(my_Exercise_3);
    vTaskSuspend(my_Exercise_4);
    vTaskStartScheduler();

    return EXIT_SUCCESS;

err_My_Exercise_2:
    vTaskDelete(my_Exercise_2);
err_My_Exercise_3:
    vTaskDelete(my_Exercise_3);
 err_My_Red_Circle:
    vTaskDelete(my_Red_Circle);
err_my_Blue_Circle:
    vTaskDelete(my_Blue_Circle);
   
err_bufferswap:
     vTaskDelete(BufferSwap);
    
err_statemachine:
    vTaskDelete(StateMachine);

err_state_queue:
        vQueueDelete(StateQueue);
    
err_screen_lock:
    vSemaphoreDelete(ScreenLock);
    
err_draw_signal:
    vSemaphoreDelete(DrawSignal);
    
err_buttons_lock:
    vSemaphoreDelete(buttons.lock);
   
err_init_audio:
     tumSoundExit();
    
err_init_events:
     tumEventExit();
    
err_init_drawing:
    tumDrawExit();
    
err_init_safe_print:
    safePrintExit();

err_my_global_values:
    vSemaphoreDelete(my_global_values.lock);

err_binary_semaphore:
    vSemaphoreDelete(Button_F);
err_my_LockIndex:
    vSemaphoreDelete(my_LockIndex);
err_my_LockOutput:
    vSemaphoreDelete(my_LockOutput);
err_my_wake_up_3:
    vSemaphoreDelete(my_wake_up_3);

err_my_global_just_for_my_exercise_3:
    vSemaphoreDelete(my_global_just_for_my_exercise_3.lock);

err_My_Seconds:
    vTaskDelete(Seconds);

err_task_binary_semaphore_take_button:
    vTaskDelete(TaskBinarySemaphoreTakeButton);
err_TaskTakeNotify:
    vTaskDelete(TaskTakeNotify);

err_My_task_1:
    vTaskDelete(My_task_1);
err_My_task_2:
    vTaskDelete(My_task_2);
err_My_task_3:
    vTaskDelete(My_task_3);
err_My_task_4:
    vTaskDelete(My_task_4);
err_My_Exercise_4:
    vTaskDelete(My_Exercise_4);



    return EXIT_FAILURE;
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