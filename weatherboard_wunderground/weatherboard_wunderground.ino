

// This is a fork of the
// USB Weather Board V3 firmware
// originally written by
// Mike Grusin, SparkFun Electronics
// www.sparkfun.com
// This version implements daily resetting of accumulated rain, wind maxima etc as per the Sparkfun Wireless Weather station https://learn.sparkfun.com/tutorials/weather-station-wirelessly-connected-to-wunderground
// This version also implements a self-switching back up power supply for a solar charging system
// This fork written by Craig Ruaux, with code included from the WIMP station by Nate Siedle, linked above.

// Compile and load onto SparkFun USB Weather Board V3 using Arduino development envrionment,
// Download from www.arduino.cc
// Tools/Board: "Arduino Pro or Pro Mini (3.3V, 8MHz) w/ATmega 328"

// Uses the SHT15x library by Jonathan Oxer et.al.
// Supplied with this software distribution, or download from https://github.com/practicalarduino/SHT1x.
// Place in your Arduino sketchbook under "libraries/SHT1x"

// Uses the SFE_BMP085 library by SparkFun with math from http://wmrx00.sourceforge.net/Arduino/BMP085-Calcs.pdf
// Supplied with this distribution; place in your Arduino sketchbook under "libraries/SFE_BMP085"

// License:
// This code is free to use, change, improve, even sell!  All we ask for is two things:
// 1. That you give SparkFun credit for the original code,
// 2. If you sell or give it away, you do so under the same license so others can do the same thing.
// More at http://creativecommons.org/licenses/by-sa/3.0/

// Have fun! 
// -your friends at SparkFun

//  Code for TSL2561 light sensor added by Craig Ruaux
//  Using libraries from Adafruit http://adafruit.com/products/439
//  TSL2561 Library from https://github.com/adafruit/TSL2561-Arduino-Library
//  Used under CC-BY-SA 3.0


// Revision history
// 1.2 Update all code to be compatible with Arduino 1.0 2012/1/23
// 1.1 changed sample_rate to 32-bit, max = 4294966 seconds (47 days)
//     RAM is also getting tight, so removed some error strings and added RAM gauge to menu 2011/08/01
// 1.0 initial release, 2011/06/27

// firmware version
const char version_major = 1;
const char version_minor = 2;

// external libraries
#include <SHT1x.h> // SHT15 humidity sensor library
#include <SFE_BMP085.h> // BMP085 pressure sensor library
#include <Wire.h> // I2C library (necessary for pressure sensor)
#include <avr/eeprom.h> // extended EEPROM read/write functions
#include "TSL2561.h"  // TSL2561 External luminosity sensor

// digital I/O pins
// (the following three are predefined)
// const int SCK = 13;
// const int MISO = 12;
// const int MOSI = 11;
const int XCLR = 9;
const int EOC = 8;
const int RF_RTS = 6;
const int RF_CTS = 5;
const int STATUSLED = 4;
const int WSPEED = 3;
const int RAIN = 2;
const int chargePin = 12;   //Using the MOSI pin, pin 4 on ICSP header, to switch Adafruit solar LiPo charging circuit as needed

// analog I/O pins
const int LIGHT = 7;
const int BATT_LVL = 6;
const int WDIR = 0;

// global variables
// Daily totals variables from WIMP Firmware
long lastSecond; //The millis counter to see when a second rolls by
unsigned int minutesSinceLastReset; //Used to reset variables after 24 hours. Imp should tell us when it's midnight, this is backup.
byte seconds; //When it hits 60, increase the current minute
byte seconds_2m; //Keeps track of the "wind speed/dir avg" over last 2 minutes array of data
byte minutes; //Keeps track of where we are in various arrays of data
byte minutes_10m; //Keeps track of where we are in wind gust/dir over last 10 minutes array of data

long lastWindCheck = 0;
volatile long lastWindIRQ = 0;
volatile byte windClicks = 0;

//We need to keep track of the following variables:
//Wind speed/dir each update (no storage)
//Wind gust/dir over the day (no storage)
//Wind speed/dir, avg over 2 minutes (store 1 per second)
//Wind gust/dir over last 10 minutes (store 1 per minute)
//Rain over the past hour (store 1 per minute)
//Total rain over date (store one per day)

byte windspdavg[120]; //120 bytes to keep track of 2 minute average
#define WIND_DIR_AVG_SIZE 120
int winddiravg[WIND_DIR_AVG_SIZE]; //120 ints to keep track of 2 minute average
float windgust_10m[10]; //10 floats to keep track of largest gust in the last 10 minutes
int windgustdirection_10m[10]; //10 ints to keep track of 10 minute max
volatile float rainHour[60]; //60 floating numbers to keep track of 60 minutes of rain

//These are all the weather values that wunderground expects:
int winddir; // [0-360 instantaneous wind direction]
float windspeedmph; // [mph instantaneous wind speed]
float windgustmph; // [mph current wind gust, using software specific time period]
int windgustdir; // [0-360 using software specific time period]
float windspdmph_avg2m; // [mph 2 minute average wind speed mph]
int winddir_avg2m; // [0-360 2 minute average wind direction]
float windgustmph_10m; // [mph past 10 minutes wind gust mph ]
int windgustdir_10m; // [0-360 past 10 minutes wind gust direction]
float humidity; // [%]
float tempf; // [temperature F]
float rainin; // [rain inches over the past hour)] -- the accumulated rainfall in the past 60 min
volatile float dailyrainin; // [rain inches so far today in local time]
//float baromin = 30.03;// [barom in] - It's hard to calculate baromin locally, do this in the agent
float pressure;
//float dewptf; // [dewpoint F] - It's hard to calculate dewpoint locally, do this in the agent


// Measurement variables
float SHT15_humidity;
float SHT15_temp;
float SHT15_dewpoint;
double BMP085_pressure;
double BMP085_temp;
float TEMT6000_light;
float WM_wspeed;  //Superceded by windspeedmph
float WM_wdirection;  //Superceded by winddir
float WM_rainfall = 0.0;
float batt_volts;
float TSL2561_lux;
int LED = 0; // status LED
unsigned int windRPM, stopped;
float light_lvl;
float batt_lvl;

// volatiles are subject to modification by IRQs
volatile unsigned long tempwindRPM, windtime, windlast, windinterval;
volatile unsigned char windintcount;
volatile boolean gotwspeed;
volatile unsigned long raintime, rainlast, raininterval, rain;

// constant conversion factors
const int BATT_RATIO = 63.3271; // divide ADC from BATT_LVL by this to get volts
const float WIND_RPM_TO_MPH = 22.686745; // divide RPM by this for velocity
const float WIND_RPM_TO_MPS = 50.748803; // divide RPM by this for meters per second
const float RAIN_BUCKETS_TO_INCHES = 0.0086206896; // multiply bucket tips by this for inches
const float RAIN_BUCKETS_TO_MM = 0.21896551; // multiply bucket tips by this for mm 
const unsigned int ZERODELAY = 4000; // ms, zero RPM if no result for this time period (see irq below)

// sensor objects
SHT1x humidity_sensor(A4, A5);
SFE_BMP085 pressure_sensor(BMP_ADDR);
TSL2561 tsl(TSL2561_ADDR_FLOAT); 

// enumerated options, changed in user menu

// output format
const int CSV = 1; // default NMEA-like comma-separated values
const int ANSI = 2; // ANSI-formatted data with hardware testing
const int LCD = 3; // directly drive a SparkFun serial-enabled 16x2 LCD display

// general units
const int ENGLISH = 1; // wind speed in miles per hour, rain in inches, temperature in degrees Fahrenheit
const int SI = 2; // International System, aka the metric system. Wind speed in meters per second, rain in mm, temperature in degrees Celsius

// pressure units
const int MBAR = 1; // millibars
const int INHG = 2; // inches of mercury (US weather report standard)
const int PSI = 3; // pounds per square inch

// pressure type
const int ABSOLUTE = 1; // absolute (true) pressure, changes with altitude (ignore altitude variable)
const int RELATIVE = 2; // relative (weather) pressure, altitude effects removed (use altitude variable)

// defaults, replaced with EEPROM settings if saved
int data_format = ANSI;
int general_units = ENGLISH;
unsigned long sample_rate = 2; // sample rate (seconds per sample, 0 for as fast as possible)
int pressure_type = RELATIVE;
long altitude = 47; // fixed weather station altitude in meters, for relative (sea level) pressure measurement. Set to your locality.
int pressure_units = INHG;
boolean weather_meters_attached = true; // true if we've hooked up SparkFun's Weather Meters (SEN-08942) (set to false to remove weather meters data from output)
long baud_rate = 9600; // default baud rate

// hardware memory pointers, used by freeMemory() (see: http://www.arduino.cc/playground/Code/AvailableMemory)
/*
extern unsigned int __bss_end;
extern unsigned int __heap_start;
extern void *__brkval;

int freeMemory()
{
  int free_memory;

  if((int)__brkval == 0)
     free_memory = ((int)&free_memory) - ((int)&__bss_end);
  else
    free_memory = ((int)&free_memory) - ((int)__brkval);

  return free_memory;
}
*/
// interrupt routines (these are called by the hardware interrupts, not by the main code)

void rainIRQ()
// if the Weather Meters are attached, count rain gauge bucket tips as they occur
// activated by the magnet and reed switch in the rain gauge, attached to input D2
{
  raintime = millis(); // grab current time
  raininterval = raintime - rainlast; // calculate interval between this and last event

  if (raininterval > 10) // ignore switch-bounce glitches less than 10uS after initial edge  (Bounce time reduced from 100 to 10)
  {
        dailyrainin += 0.011; //Each dump is 0.011" of water
        rainHour[minutes] += 0.011; //Increase this minute's amount of rain
        
        rainlast = raintime; // set up for next event
  }
}

// wspeedIRQ() was completely replaced by code from WIMP Station 1/3/16
void wspeedIRQ()
// Activated by the magnet in the anemometer (2 ticks per rotation), attached to input D3
{
	if (millis() - lastWindIRQ > 10) // Ignore switch-bounce glitches less than 10ms (142MPH max reading) after the reed switch closes
	{
		lastWindIRQ = millis(); //Grab the current time
		windClicks++; //There is 1.492MPH for each click per second.
	}
}

void setup()
// this procedure runs once upon startup or reboot
// perform all the settings we need before running the main loop
{
  seconds = 0;
  lastSecond = millis();
  
  // set up inputs and outputs
  pinMode(XCLR,OUTPUT); // output to BMP085 reset (unused)
  digitalWrite(XCLR,HIGH); // make pin high to turn off reset 
  
  pinMode(EOC,INPUT); // input from BMP085 end of conversion (unused)
  digitalWrite(EOC,LOW); // turn off pullup
  
  pinMode(STATUSLED,OUTPUT); // output to status LED
  
  pinMode(WSPEED,INPUT_PULLUP); // input from wind meters windspeed sensor
   
  pinMode(RAIN,INPUT_PULLUP); // input from wind meters rain gauge sensor
  

  pinMode(chargePin, OUTPUT); // output for transistor to switch charge, used in checkCharge()

  // get settings from EEPROM (use defaults if EEPROM has not been used)
  retrieveEEPROMsettings();
  
  // initialize serial port
  Serial.begin(baud_rate);
  Serial.println();
  Serial.println("RESET");

  // initialize BMP085 pressure sensor
//  if (pressure_sensor.begin() == 0)
//    error(1);

  // init wind speed interrupt global variables
  gotwspeed = false; windRPM = 0; windintcount = 0;
 
  // blink status LED 3 times
  digitalWrite(STATUSLED,HIGH);
  delay(100);
  digitalWrite(STATUSLED,LOW);
  delay(250);
  digitalWrite(STATUSLED,HIGH);
  delay(100);
  digitalWrite(STATUSLED,LOW);
  delay(250);
  digitalWrite(STATUSLED,HIGH);
  delay(100);
  digitalWrite(STATUSLED,LOW);
  delay(250);

  if (weather_meters_attached)
  {
    // attach external interrupt pins to IRQ functions
    attachInterrupt(0,rainIRQ,FALLING);
    attachInterrupt(1,wspeedIRQ,FALLING);
    
    // turn on interrupts
    interrupts();
  }
}

void loop()
// loops forever after setup() ends!
{
  //Serial.println();
 // Serial.println("In Loop");
  static long templong, windstopped;
  static unsigned long loopstart, loopend;
  double Tn, m;
  static char LCDstate;
  char status;
  
  // record current time so we can sample at regular intervals
 /* loopstart = millis();
  loopend = loopstart + (sample_rate * 1000ul);
  

  // turn on LED while we're doing measurements
  digitalWrite(STATUSLED,HIGH);
*/

//New from WIMP station firmware
//Keep track of which minute it is
	if(millis() - lastSecond >= 1000)
	{
		lastSecond += 1000;

		//Take a speed and direction reading every second for 2 minute average
		if(++seconds_2m > 119) seconds_2m = 0;

		//Calc the wind speed and direction every second for 120 second to get 2 minute average
		windspeedmph = get_wind_speed();
		winddir = get_wind_direction();
		windspdavg[seconds_2m] = (int)windspeedmph;
		winddiravg[seconds_2m] = winddir;
		//if(seconds_2m % 10 == 0) displayArrays();

		//Check to see if this is a gust for the minute
		if(windspeedmph > windgust_10m[minutes_10m])
		{
			windgust_10m[minutes_10m] = windspeedmph;
			windgustdirection_10m[minutes_10m] = winddir;
		}

		//Check to see if this is a gust for the day
		//Resets at midnight each night
		if(windspeedmph > windgustmph)
		{
			windgustmph = windspeedmph;
			windgustdir = winddir;
		}

		//Blink stat LED briefly to show we are alive
		digitalWrite(STATUSLED, HIGH);
		//reportWeather(); //Print the current readings. Takes 172ms.
		delay(25);
		digitalWrite(STATUSLED, LOW);

		//If we roll over 60 seconds then update the arrays for rain and windgust
		if(++seconds > 59)
		{
			seconds = 0;

			if(++minutes > 59) minutes = 0;
			if(++minutes_10m > 9) minutes_10m = 0;

			rainHour[minutes] = 0; //Zero out this minute's rainfall amount
			windgust_10m[minutes_10m] = 0; //Zero out this minute's gust

			minutesSinceLastReset++; //It's been another minute since last night's midnight reset
		}
	}




  // an interrupt occurred, handle it now
  if (gotwspeed)
  {
    gotwspeed = false;
    windRPM = word(tempwindRPM); // grab the RPM value calculated by the interrupt routine
    windstopped = millis() + ZERODELAY; // save this timestamp
  }

  // zero wind speed RPM if we don't get a reading in ZERODELAY ms
  if (millis() > windstopped)
  {
    windRPM = 0; windintcount = 0;
  }
  
  TWCR &= ~(_BV(TWEN));  // turn off I2C enable bit so we can access the SHT15 humidity sensor

  // get humidity and temp (SHT15)
  SHT15_temp = humidity_sensor.readTemperatureC();
  SHT15_humidity = humidity_sensor.readHumidity();

  // compute dewpoint (because we can!)
  if (SHT15_temp > 0.0)
    {Tn = 243.12; m = 17.62;}
  else
    {Tn = 272.62; m = 22.46;}

  SHT15_dewpoint = (Tn*(log(SHT15_humidity/100)+((m*SHT15_temp)/(Tn+SHT15_temp)))/(m-log(SHT15_humidity/100)-((m*SHT15_temp)/(Tn+SHT15_temp))));

  // get temp (SHT15)
  switch (general_units)
  {
    case ENGLISH: // Fahrenheit
      SHT15_temp = (SHT15_temp*9.0/5.0)+32.0;
      SHT15_dewpoint = (SHT15_dewpoint*9.0/5.0)+32.0;
      break;
    case SI: // celsius, don't need to do anything
      break;
    default:
      SHT15_temp = -1.0; // error, invalid units
      SHT15_dewpoint = -1.0; // error, invalid units
  }

  TWCR |= _BV(TWEN);  // turn on I2C enable bit so we can access the BMP085 pressure sensor

  // start BMP085 temperature reading
  status = pressure_sensor.startTemperature();
  if (status != 0)
    delay(status); // if nonzero, status is number of ms to wait for reading to become available
  else
//    error(2);
    
  // retrieve BMP085 temperature reading
  status = pressure_sensor.getTemperature(&BMP085_temp); // deg C
  if (status == 0)
 //   error(3);
  
  // start BMP085 pressure reading
  status = pressure_sensor.startPressure(3);
  if (status != 0)
    delay(status); // if nonzero, status is number of ms to wait for reading to become available
  else
 //   error(4);
    
  // retrieve BMP085 pressure reading
  status = pressure_sensor.getPressure(&BMP085_pressure, &BMP085_temp); // mbar, deg C
  if (status == 0)
//    error(5);
 
  // compensate for altitude if needed
  if (pressure_type == RELATIVE)
    BMP085_pressure = pressure_sensor.sealevel(BMP085_pressure,altitude);

  // convert to desired units
  switch (general_units)
  {
    case SI: // celsius
      // do nothing, already C
      break;
    case ENGLISH: // Fahrenheit
      BMP085_temp = BMP085_temp * 1.8 + 32.0;
      break;
    default:
      BMP085_temp = -1.0; // error, invalid units
  }

  switch (pressure_units)
  {
    case MBAR:
      // do nothing, already mbar
      break;
    case INHG:
      BMP085_pressure = BMP085_pressure / 33.8600000;
      break;
    case PSI:
      BMP085_pressure = BMP085_pressure / 68.9475728;
      break;
    default:
      BMP085_pressure = -1.0; // error, invalid units
  }

  // get light
  TEMT6000_light = (1023.0 - float(analogRead(LIGHT))) / 10.23; // 0-100 percent

  // windspeed unit conversion
  switch (general_units)
  {
    case SI: // meters per second
      WM_wspeed = float(windRPM) / WIND_RPM_TO_MPS;
      break;
    case ENGLISH: // miles per hour
      WM_wspeed = float(windRPM) / WIND_RPM_TO_MPH;
      break;
    default:
      WM_wspeed = -1.0; // error, invalid units
  }

  // get wind direction
  WM_wdirection = get_wind_direction();

  // rainfall unit conversion
  switch (general_units)
  {
    case SI: // mm
      WM_rainfall = rain * RAIN_BUCKETS_TO_MM;
      break;
    case ENGLISH: // inches
      WM_rainfall = rain * RAIN_BUCKETS_TO_INCHES;
      break;
    default:
      WM_rainfall = -1.0; // error, invalid units
  }

  // get battery voltage
  batt_volts = float(analogRead(BATT_LVL)) / BATT_RATIO;

  // below are a bunch of nested switch statements to handle the different output data_formats that are possible
  // feel free to modify them or add your own!

 /*
Removed with change to WIMP code, 1/3/16
 switch (data_format)
  {

    case CSV: // data_format: comma-separated values  Altered to report one at a time.
    {
      // number after values is number of digits after decimal point to print
      Serial.print("$");
      printComma();
      Serial.print(SHT15_temp,1);
      printComma();
      Serial.print(SHT15_humidity,0);
      printComma();
      Serial.print(SHT15_dewpoint,1);
      printComma();
      switch (pressure_units) // change decimal point for different units
      {
        case MBAR:
          Serial.print(BMP085_pressure,2);
          break;
        case INHG:
          Serial.print(BMP085_pressure,3);
          break;
        case PSI:
          Serial.print(BMP085_pressure,4);
          break;
      }
      printComma();
      // Serial.print(BMP085_temp,1);  // for CSV format, we'll only output the SHT15 temperature
      // Serial.print(",");
      //Serial.print(TEMT6000_light,1);  //Using luminance detector - CR
     // printComma();
      if (weather_meters_attached)
      {
        Serial.print(WM_wspeed,1);
        printComma();
        Serial.print(WM_wdirection,0);
        printComma();
        switch (general_units) // change decimal point for different units
        {
          case ENGLISH:
            Serial.print(WM_rainfall,2);
            break;
          case SI:
            Serial.print(WM_rainfall,1);
            break;
        }
        printComma();
      }
      Serial.print(batt_volts,2);
     // printComma();
     Serial.print('\n');  //Using a LF character to indicate end of the CSV sentence - C Ruaux
     // Serial.println();
    }
    break;
//  took out unused options for final vers

  }

  // turn off LED (done with measurements)
 // digitalWrite(STATUSLED,LOW);
*/
 checkCharge();

/*  // we're done sampling all the sensors and printing out the results
  // now wait in a loop for the next sample time
  // while we're waiting, we'll check the serial port to see if the user has pressed CTRL-Z to activate the menu
  do // this is a rare instance of do-while - we need to run through this loop at least once to see if CTRL-Z has been pressed
  {
    while (Serial.available())
    {
      if (Serial.read() == 0x1A) // CTRL-Z
      {
        menu(); // display the menu and allow settings to be changed
        loopend = millis(); // we're done with the menu, break out of the do-while
      }
    }
  }
    while(millis() < loopend);
*/    

	//Wait for the Parser/Uploader to ping us with the ! character
	if(Serial.available())
	{
		byte incoming = Serial.read();
		if(incoming == '!')
		{
			reportWeather(); //Send all the current readings out over serial
	    	}
	
	else if(incoming == '@') //Special character from Imp indicating midnight local time
		{
			midnightReset(); //Reset a bunch of variables like rain and daily total rain
		}
        }
}


int get_wind_direction() 
// read the wind direction sensor, return heading in degrees
{
  unsigned int adc;
  
  adc = averageAnalogRead(WDIR); // get the current reading from the sensor
  
  // The following table is ADC readings for the wind direction sensor output, sorted from low to high.
  // Each threshold is the midpoint between adjacent headings. The output is degrees for that ADC reading.
  // Note that these are not in compass degree order!  See Weather Meters datasheet for more information.
  
  if (adc < 380) return (112.5);
  if (adc < 393) return (67.5);
  if (adc < 414) return (90);
  if (adc < 456) return (157.5);
  if (adc < 508) return (135);
  if (adc < 551) return (202.5);
  if (adc < 615) return (180);
  if (adc < 680) return (22.5);
  if (adc < 746) return (45);
  if (adc < 801) return (247.5);
  if (adc < 833) return (225);
  if (adc < 878) return (337.5);
  if (adc < 913) return (0);
  if (adc < 940) return (292.5);
  if (adc < 967) return (315);
  if (adc < 990) return (270);
  return (-1); // error, disconnected?
}

/* From Weather Meters docs and the Weather Board V3 schematic:

heading         resistance      volts           nominal         midpoint (<)
112.5	º	0.69	k	1.2	V	372	counts	380
67.5	º	0.89	k	1.26	V	389	counts	393
90	º	1	k	1.29	V	398	counts	414
157.5	º	1.41	k	1.39	V	430	counts	456
135	º	2.2	k	1.56	V	483	counts	508
202.5	º	3.14	k	1.72	V	534	counts	551
180	º	3.9	k	1.84	V	569	counts	615
22.5	º	6.57	k	2.13	V	661	counts	680
45	º	8.2	k	2.26	V	700	counts	746
247.5	º	14.12	k	2.55	V	792	counts	801
225	º	16	k	2.62	V	811	counts	833
337.5	º	21.88	k	2.76	V	855	counts	878
0	º	33	k	2.91	V	902	counts	913
292.5	º	42.12	k	2.98	V	925	counts	940
315	º	64.9	k	3.08	V	956	counts	967
270	º	98.6	k	3.15	V	978	counts	>967
*/

int averageAnalogRead(int pinToRead)  //From WIMP firmware
{
	byte numberOfReadings = 8;
	unsigned int runningValue = 0;

	for(int x = 0 ; x < numberOfReadings ; x++)
		runningValue += analogRead(pinToRead);
	runningValue /= numberOfReadings;

	return(runningValue);
}


char getChar()
// wait for one character to be typed (and convert to uppercase if it's alphabetic)
{
  digitalWrite(STATUSLED,HIGH);
  while (!Serial.available())
    {;} // wait here forever for a character
  digitalWrite(STATUSLED,LOW);
  return(toupper(Serial.read())); // return the upper case character
}

long getLong()
// wait for a number to be input (end with return), allows backspace and negative
{
  char mystring[10];
  char mychar;
  int x = 0;
  boolean done = false;
  
  // input a string of characters from the user
  
  while (!done)
  {
    mychar = getChar();
    if ((mychar == 0x0D) || (mychar == 0x0A)) // carriage return or line feed?
    {
      // terminate the string with 0x00 and exit
      mystring[x] = 0;
      done = true;
    }
    else
    {
      if ((mychar == 0x08) && (x > 0)) // backspace?
      {
        // simulate a backspace - back up, print a space to erase character, and backspace again
        Serial.write(0x08);
        Serial.print(" ");
        Serial.write(0x08);
        x--;
      }
      else // a real character?
      {
//        if ((mychar != 0x08) && (x < 10)) 
        if (x < 10)
        {
          Serial.print(mychar);
          mystring[x] = mychar;
          x++;
        }
      }
    }
  }
  // convert string to long using ASCII-to-long standard function
  return(atol(mystring));
}

void storeEEPROMsettings()
// store all the user-changable settings in EEPROM so it survives power cycles
// note that ints are two bytes, longs are four
{
  eeprom_write_word((uint16_t*)0,data_format);
  eeprom_write_word((uint16_t*)2,general_units);
//  eeprom_write_word((uint16_t*)4,sample_rate); // this space available for an int (changed sample rate to long)
  eeprom_write_word((uint16_t*)6,pressure_units);
  eeprom_write_word((uint16_t*)8,pressure_type);
  eeprom_write_dword((uint32_t*)10,altitude);
  eeprom_write_dword((uint32_t*)14,baud_rate);
  eeprom_write_word((uint16_t*)18,(int)weather_meters_attached);
  eeprom_write_dword((uint32_t*)22,sample_rate);
}

void retrieveEEPROMsettings()
// retrieve settings previously stored in EEPROM
// only load into variables if the settings are valid (-1 == 0xFF == erased)
// note that ints are two bytes, longs are four
{
  int tempint;
  long templong;
  
  // don't initialize variables if EEPROM is unused
  // (uninitialized EEPROM values read back as -1)
  tempint = eeprom_read_word((uint16_t*)0); if (tempint != -1) data_format = tempint;
  tempint = eeprom_read_word((uint16_t*)2); if (tempint != -1) general_units = tempint;
//  tempint = eeprom_read_word((uint16_t*)4); if (tempint != -1) sample_rate = tempint; // this space available for an int (changed sample rate to long)
  tempint = eeprom_read_word((uint16_t*)6); if (tempint != -1) pressure_units = tempint;
  tempint = eeprom_read_word((uint16_t*)8); if (tempint != -1) pressure_type = tempint;
  templong = eeprom_read_dword((uint32_t*)10); if (templong != -1) altitude = templong;
  templong = eeprom_read_dword((uint32_t*)14); if (templong != -1) baud_rate = templong;
  tempint = eeprom_read_word((uint16_t*)18); if (tempint != -1) weather_meters_attached = (boolean)tempint;
  templong = eeprom_read_dword((uint32_t*)22); if (templong != -1) sample_rate = templong;
}

//Returns the instataneous wind speed
float get_wind_speed()
{
	float deltaTime = millis() - lastWindCheck; //750ms

	deltaTime /= 1000.0; //Covert to seconds

	float windSpeed = (float)windClicks / deltaTime; //3 / 0.750s = 4

	windClicks = 0; //Reset and start watching for new wind
	lastWindCheck = millis();

	windSpeed *= 1.492; //4 * 1.492 = 5.968MPH

	/* Serial.println();
	 Serial.print("Windspeed:");
	 Serial.println(windSpeed);*/

	return(windSpeed);
}


void printComma() // we do this a lot, it saves two bytes each time we call it
{
  Serial.print(",");
}

void checkCharge()
{

// local variables  
boolean chargeState;
long now=millis();
long chargeStart;  //millis value for start of charging

if (batt_volts<3.5)
{
  if (chargeState==false)
  {
  digitalWrite(chargePin, HIGH);  //switch in power supply through battery charger
  chargeStart = millis(); 
  chargeState = true;
  }
  else
  if (chargeState==true)
  {
    if ((now-chargeStart)>3600000)   //have we been charging for > one hour?
    {
      digitalWrite(chargePin, LOW); //switch off power supply
      chargeState=false;
   }
  }
 }
}

//Calculates each of the variables that wunderground is expecting
void calcWeather()
{
	//current winddir, current windspeed, windgustmph, and windgustdir are calculated every 100ms throughout the day

	//Calc windspdmph_avg2m
	float temp = 0;
	for(int i = 0 ; i < 120 ; i++)
		temp += windspdavg[i];
	temp /= 120.0;
	windspdmph_avg2m = temp;

	//Calc winddir_avg2m, Wind Direction
	//You can't just take the average. Google "mean of circular quantities" for more info
	//We will use the Mitsuta method because it doesn't require trig functions
	//And because it sounds cool.
	//Based on: http://abelian.org/vlf/bearings.html
	//Based on: http://stackoverflow.com/questions/1813483/averaging-angles-again
	long sum = winddiravg[0];
	int D = winddiravg[0];
	for(int i = 1 ; i < WIND_DIR_AVG_SIZE ; i++)
	{
		int delta = winddiravg[i] - D;

		if(delta < -180)
			D += delta + 360;
		else if(delta > 180)
			D += delta - 360;
		else
			D += delta;

		sum += D;
	}
	winddir_avg2m = sum / WIND_DIR_AVG_SIZE;
	if(winddir_avg2m >= 360) winddir_avg2m -= 360;
	if(winddir_avg2m < 0) winddir_avg2m += 360;


	//Calc windgustmph_10m
	//Calc windgustdir_10m
	//Find the largest windgust in the last 10 minutes
	windgustmph_10m = 0;
	windgustdir_10m = 0;
	//Step through the 10 minutes
	for(int i = 0; i < 10 ; i++)
	{
		if(windgust_10m[i] > windgustmph_10m)
		{
			windgustmph_10m = windgust_10m[i];
			windgustdir_10m = windgustdirection_10m[i];
		}
	}

	//Calc humidity
	humidity = SHT15_humidity;
	//float temp_h = myHumidity.readTemperature();
	//Serial.print(" TempH:");
	//Serial.print(temp_h, 2);

	//Calc tempf from pressure sensor
	tempf = SHT15_temp;
	//Serial.print(" TempP:");
	//Serial.print(tempf, 2);

	//Total rainfall for the day is calculated within the interrupt
	//Calculate amount of rainfall for the last 60 minutes
	rainin = 0;
	for(int i = 0 ; i < 60 ; i++)
		rainin += rainHour[i];

	//Calc pressure
	pressure = BMP085_pressure;

	//Calc dewptf

	//Calc light level
	light_lvl = TEMT6000_light;

	
}


  //Reports the weather string to the Uploader/Parser Board
void reportWeather()
{
	calcWeather(); //Go calc all the various sensors

	Serial.print("$,winddir=");
	Serial.print(winddir);
	Serial.print(",windspeedmph=");
	Serial.print(windspeedmph, 1);
	Serial.print(",windgustmph=");
	Serial.print(windgustmph, 1);
	Serial.print(",windgustdir=");
	Serial.print(windgustdir);
	Serial.print(",windspdmph_avg2m=");
	Serial.print(windspdmph_avg2m, 1);
	Serial.print(",winddir_avg2m=");
	Serial.print(winddir_avg2m);
	Serial.print(",windgustmph_10m=");
	Serial.print(windgustmph_10m, 1);
	Serial.print(",windgustdir_10m=");
	Serial.print(windgustdir_10m);
	Serial.print(",humidity=");
	Serial.print(humidity, 1);
	Serial.print(",tempf=");
	Serial.print(tempf, 1);
	Serial.print(",rainin=");
	Serial.print(rainin, 2);
	Serial.print(",dailyrainin=");
	Serial.print(dailyrainin, 2);
	Serial.print(",pressure="); 
	Serial.print(pressure, 2);
	Serial.print(",batt_lvl=");
	Serial.print(batt_lvl, 2);
	Serial.print(",light_lvl=");
	Serial.print(light_lvl, 2);


	Serial.print(",");
	Serial.println("#,");

	//Test string
	//Serial.println("$,winddir=270,windspeedmph=0.0,windgustmph=0.0,windgustdir=0,windspdmph_avg2m=0.0,winddir_avg2m=12,windgustmph_10m=0.0,windgustdir_10m=0,humidity=998.0,tempf=-1766.2,rainin=0.00,dailyrainin=0.00,-999.00,batt_lvl=16.11,light_lvl=3.32,#,");
}

//When the parser tells us it's midnight, reset the total amount of rain and gusts
void midnightReset()
{
	dailyrainin = 0; //Reset daily amount of rain

	windgustmph = 0; //Zero out the windgust for the day
	windgustdir = 0; //Zero out the gust direction for the day

	minutes = 0; //Reset minute tracker
	seconds = 0;
	lastSecond = millis(); //Reset variable used to track minutes

	minutesSinceLastReset = 0; //Zero out the backup midnight reset variable
}

