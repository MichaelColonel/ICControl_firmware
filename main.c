/*
 *      This program is free software; you can redistribute it and/or modify
 *      it under the terms of the GNU General Public License as published by
 *      the Free Software Foundation; either version 2 of the License, or
 *      (at your option) any later version.
 *
 *      This program is distributed in the hope that it will be useful,
 *      but WITHOUT ANY WARRANTY; without even the implied warranty of
 *      MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *      GNU General Public License for more details.
 *
 *      You should have received a copy of the GNU General Public License
 *      along with this program; if not, write to the Free Software
 *      Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 *      MA 02110-1301, USA.
 */

// 8 MHz RC-oscillator
// Fuse bytes E:0xFF, H:0xC9, L:0xE4 -- Disable JTAG, Disable ATmega103 compatibility mode

// AVRDude for fuse bytes (8 MHz RC-oscillator)
// avrdude -pm128 -cavr910 -P/dev/ttyACM_AVR910 -b4800 -u -Uhfuse:w:0xC9:m -Ulfuse:w:0xE4:m -Uefuse:w:0xFF:m

// AVRDude for flash hex firmware
// avrdude -pm128 -cavr910 -P/dev/ttyACM_AVR910 -b4800 -Uflash:w:Cabin26A_IC.hex:a

#include <avr/io.h>
#include <avr/interrupt.h>
#include <avr/pgmspace.h>

#include <util/atomic.h>
#include <util/delay.h>
#include <util/crc16.h>

#include <ctype.h>
#include <stdint.h>
#include <limits.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>

#define SETBITS( x, y)                           ((x) |= (y))
#define CLEARBITS( x, y)                        ((x) &= ~(y))
#define TOGGLEBITS( x, y)                        ((x) ^= (y))
#define SETBIT( x, y)                     SETBITS( x, _BV(y))
#define CLEARBIT( x, y)                 CLEARBITS( x, _BV(y))
#define TOGGLEBIT( x, y)               TOGGLEBITS( x, _BV(y))
#define BITSSET( x, y)                   (((x) & (y)) == (y))
#define BITSCLEAR( x, y)                   (((x) & (y)) == 0)
#define BITVAL( x, y)                      (((x) >> (y)) & 1)

#define SETVAL( x, y, value) ((value) ? SETBIT( x, y) : CLEARBIT( x, y))

#ifndef F_CPU
#define F_CPU                                                 8000000UL
#endif

#define BAUDRATE                                                  38400
#define PRESCALE                        (F_CPU / (BAUDRATE * 16UL) - 1)
#define BUFFER                                                        8

#define CLOCK                                                         1
#define PRESCALER                                                  1024
#define VALUE                   (F_CPU / (2UL * PRESCALER * CLOCK) - 1)
#define CALC_VALUE( P, F)               (F_CPU / (2UL * (P) * (F)) - 1)

#define DATA_SIZE 4

#define CHIPS                                              12
#define CHANNELS_PER_CHIP                                  32
#define BYTES_PER_ADC_COUNT                                 4
#define COUNTS                                             42
#define INTEGRATION_TIME_CODE_MAX                          16
#define CAPACITY_CODE_OFFSET                                5

#define SAMPLES(C,IT)          ((C) * CHANNELS_PER_CHIP * BYTES_PER_ADC_COUNT * 2UL * (IT))
#define DEFAULT_SAMPLES                        SAMPLES(CHIPS, COUNTS)
#define COUNTS_MIN                                          10
#define ACQ_LOOP_CYCLES                                    150

const char OK_string[] PROGMEM = "OK";
const char NO_string[] PROGMEM = "NO";
const char Start_string[] PROGMEM = "Start";
const char Finish_string[] PROGMEM = "Finish";
const char Abort_string[] PROGMEM = "Abort";
const char Welcome_string[] PROGMEM = "Welcome";

PGM_P const strings[] PROGMEM = {
  OK_string,
  NO_string,
  Start_string,
  Finish_string,
  Abort_string,
  Welcome_string
};

volatile char code = 'N';
volatile uint8_t data = 0;
volatile uint16_t chips_enabled = 0x0FFF;
volatile uint16_t default_samples = 0;

static uint8_t nofchips = CHIPS; // must always be 12
static uint8_t integration_time = 1; // integration time code (0...15)
static uint8_t chip_capacity = 7;
static uint32_t samples = DEFAULT_SAMPLES;
static bool use_external_start = false;
static bool single_shot_acquisition = false;
static bool adc_format = false; // ADC FORMAT (0 === 16bit, 1 === 20bit)

void init(void) __attribute__((naked,section(".init3")));
static void ft2232h_b_write_rom_string(PGM_P str);
static void ft2232h_b_write_rom_string_number(uint8_t num);
static void ft2232h_b_write_char(char c);
static void ft2232h_a_write_strobe(void);

static void setup_chips_enabled(void);
static void setup_integration_time(void);
static void setup_ddc232_configuration_register(void);
static void update_code(uint8_t cmd);

static uint8_t get_chips_enabled(void);

// 1 second LED0 toggle timeout
ISR(TIMER3_COMPA_vect) // timer/counter-3 compare interrupt
{
  TOGGLEBIT( PORTD, PD7); // LED0
}

ISR(INT1_vect) // INT1 interrupt
{
  CLEARBIT( EIMSK, INT1); // Disable INT1
  CLEARBIT( PORTB, PB4); // ALTERA reset - low
  SETBIT( PORTB, PB4); // ALTERA reset - high
  code = 'B';
}

ISR(INT3_vect) // INT3 interrupt (FT2232H - Channel B interruption signal)
{
  static uint8_t pos;
  static bool bufferIsReset;
  static uint8_t buffer[3];
  PORTA = 0xFF; // Port A - Input
  loop_until_bit_is_clear( PIND, PIND3); // Wait Channel B RXF# ready to read
  CLEARBIT( PORTC, PC6); // Channel B RD# - Low level
  _delay_loop_1(1);
  buffer[pos++] = PINA;
  SETBIT( PORTC, PC6); //  Channel B RD# - High level
  _delay_loop_1(1);
  PORTA = 0x00; // Port A - Hi-Z
  if (pos == 3)
  {
	TOGGLEBIT( PORTG, PG1); // LED2
    pos = 0;
    if (bufferIsReset)
    {
      switch (buffer[0])
      {
      case 'B': // Begin acquisition
      case 'G': // write DDC232 confiGuration register
      case 'R': // ALTERA Reset
      case 'H': // cHip reset
      case 'S': // Single shot acquisition
      case 'L': // get List of chips enabled
        code = buffer[0];
    	break;
      case 'A': // external stArt
      case 'O': // set number Of chips
      case 'C': // set Capacity for chip
      case 'I': // Integration time
      case 'M': // aMount of samples
      case 'D': // ADC moDe
        code = buffer[0];
        data = buffer[1];
        break;
      case 'E': // chips Enabled
        code = buffer[0];
        chips_enabled = (buffer[2] << CHAR_BIT) | buffer[1];
    	break;
      case 'P': // new amount of samPles
        code = buffer[0];
        default_samples = (buffer[2] << CHAR_BIT) | buffer[1];
        break;
      default:
        break;
      }
    }
    else
    {
      TOGGLEBIT( PORTG, PG0); // LED1
      bufferIsReset = true;
      code = 'Z';
    }
  }
}
/*
ISR(INT4_vect) // INT4 interrupt
{
}
*/
int main(int argc, char** argv)
{
  while (1)
  {
    uint8_t cmd;
	// Wait for interrupt and value other than 'N'
	do
	{
	  ATOMIC_BLOCK(ATOMIC_RESTORESTATE)
	  {
	    cmd = code;
	  }
	} while (cmd == 'N');

    switch (cmd)
	{
	case 'A': // external start
	  use_external_start = (bool)data;
	  single_shot_acquisition = false;
	  SETBIT( EIFR, INTF1); // Reset INT1
	  SETVAL( EIMSK, INT1, use_external_start); // enable INT1 if use_external start is true
	  ft2232h_b_write_char('A');
	  ft2232h_b_write_char('0' + use_external_start);
	  ft2232h_b_write_rom_string_number(0); // "OK"
	  update_code(cmd);
	  break;
    case 'B':
      if (bit_is_set(EIMSK, INT1))
      {
        CLEARBIT( EIMSK, INT1); // Disable INT1
      }
      ft2232h_b_write_rom_string_number(2); // "Start"
      _delay_ms(10);
      CLEARBIT( PORTB, PB5); // READ_DATA == 0
      SETBIT( PORTB, PB3); // START acquisition == 1
      for (uint8_t i = 0; i < ACQ_LOOP_CYCLES; ++i)
      {
        _delay_ms(10);
        if (code != 'B')
        {
          goto ext_abort;
        }
      }
      CLEARBIT( PORTB, PB3); // START acquisition == 0
      _delay_ms(50);
      SETBIT( PORTB, PB5); // READ_DATA == 1
      // ALTERA RESET
      CLEARBIT( PORTB, PB4); // ALTERA reset - low
      SETBIT( PORTB, PB4); // ALTERA reset - high

      for (uint32_t j = 0; j < samples; ++j)
      {
        if (code != 'B')
        {
          goto ext_abort;
        }
        // Channel A write strobe
        ft2232h_a_write_strobe();
        // READ_DATA_CLK strobe
        SETBIT( PORTB, PB6); // READ_DATA_CLK - High
        CLEARBIT( PORTB, PB6); // READ_DATA_CLK - Low
      }

      CLEARBIT( PORTB, PB5); // READ_DATA - Low
      if (use_external_start && !single_shot_acquisition)
      {
    	SETBIT( EIFR, INTF1); // Reset INT1
        SETBIT( EIMSK, INT1); // Enable INT1
      }
      else if (single_shot_acquisition)
      {
        single_shot_acquisition = false;
      }
      ft2232h_b_write_rom_string_number(3); // "Finish"
      update_code(cmd);
      break;
ext_abort:
      CLEARBIT( PORTB, PB3); // START acquisition == 0
      CLEARBIT( PORTB, PB5); // READ_DATA == 0
      if (use_external_start && !single_shot_acquisition)
      {
    	SETBIT( EIFR, INTF1); // Reset INT1
        SETBIT( EIMSK, INT1); // Enable INT1
      }
      else if (single_shot_acquisition)
      {
        single_shot_acquisition = false;
      }
      ft2232h_b_write_rom_string_number(4); // "Abort"
      break; // exit to main loop to execute a new command code
    case 'C':
      chip_capacity = data >> CAPACITY_CODE_OFFSET;
      ft2232h_b_write_char('C');
      ft2232h_b_write_char('0' + chip_capacity);
      ft2232h_b_write_rom_string_number(0); // "OK"
      update_code(cmd);
      break;
    case 'D':
      adc_format = (bool)data;
//      SETVAL( PORTF, PF4, adc_format); // ADC FORMAT (0 === 16bit, 1 === 20bit)
      ft2232h_b_write_char('D');
      ft2232h_b_write_char('0' + adc_format);
      ft2232h_b_write_rom_string_number(0); // "OK"
      update_code(cmd);
      break;
    case 'E': // chips Enabled
      {
        uint8_t pos = 0;
        if (chips_enabled && chips_enabled <= 0x0FFF)
        {
          setup_chips_enabled();
        }
        else
        {
          pos = 1;
        }
        ft2232h_b_write_char('E');
        ft2232h_b_write_rom_string_number(pos); // "OK" if 0, "NO" if 1
      }
      update_code(cmd);
      break;
    case 'G': // setup capacity, ADC format, etc.
      setup_ddc232_configuration_register();
      ft2232h_b_write_char('G');
      ft2232h_b_write_rom_string_number(0); // "OK"
      update_code(cmd);
      break;
    case 'H': // Chip RESET strobe
      CLEARBIT( PORTG, PG3); // Chip RESET - low
      _delay_ms(2);
      SETBIT( PORTG, PG3); // Chip RESET - high
      ft2232h_b_write_char('H');
      ft2232h_b_write_rom_string_number(0); // "OK"
      update_code(cmd);
      break;
    case 'I':
      {
        uint8_t pos = 0;
        if (data < INTEGRATION_TIME_CODE_MAX)
        {
          integration_time = data;
          setup_integration_time();
        }
        else
        {
          pos = 1;
        }
        ft2232h_b_write_char('I');
        ft2232h_b_write_char('A' + integration_time);
        ft2232h_b_write_rom_string_number(pos); // "OK" if 0, "NO" if 1
      }
      update_code(cmd);
      break;
    case 'L':
      ft2232h_b_write_char('L');
      for (uint8_t i = 0; i < CHIPS; ++i)
      {
        char chip = (chips_enabled >> i) & 1;
        chip += '0';
        ft2232h_b_write_char(chip);
      }
      ft2232h_b_write_rom_string_number(0); // "OK"
      update_code(cmd);
      break;
    case 'M':
      {
        uint8_t pos = 0;
        uint8_t chips = get_chips_enabled();
        if (data >= COUNTS_MIN && data <= UCHAR_MAX && chips)
        {
          samples = SAMPLES(chips, data);
        }
        else
        {
          pos = 1;
        }
        ft2232h_b_write_char('M');
        ft2232h_b_write_char('A' + chips);
        ft2232h_b_write_rom_string_number(pos); // "OK" if 0, "NO" if 1
      }
      update_code(cmd);
      break;
    case 'P': // new amount of samPles
      {
        uint8_t pos = 0;
        uint8_t chips = get_chips_enabled();
        if (default_samples && chips)
        {
          samples = SAMPLES(chips, default_samples);
        }
        else
        {
          pos = 1;
        }
        ft2232h_b_write_char('P');
        ft2232h_b_write_rom_string_number(pos); // "OK" if 0, "NO" if 1
      }
      update_code(cmd);
      break;
    case 'O':
      {
        uint8_t pos = 0;
        if (data && data <= CHIPS)
        {
          nofchips = data; // not used any more
        }
        else
        {
          pos = 1;
        }
        ft2232h_b_write_char('O');
        ft2232h_b_write_char('A' + nofchips);
        ft2232h_b_write_rom_string_number(pos); // "OK" if 0, "NO" if 1
      }
      update_code(cmd);
      break;
    case 'S': // single shot acquisition (external start)
      single_shot_acquisition = true;
      SETBIT( EIFR, INTF1); // Reset INT1
      SETBIT( EIMSK, INT1); // Enable INT1
      ft2232h_b_write_char('S');
      ft2232h_b_write_rom_string_number(0); // "OK"
      update_code(cmd);
      break;
    case 'R': // ALTERA RESET strobe
      CLEARBIT( PORTB, PB4); // ALTERA reset - low
      SETBIT( PORTB, PB4); // ALTERA reset - high
      ft2232h_b_write_char('R');
      ft2232h_b_write_rom_string_number(0); // "OK"
      update_code(cmd);
      break;
	case 'Z': // initial "Welcome" message
	  ft2232h_b_write_rom_string_number(5); // "Welcome"
	  update_code(cmd);
	  break;
	case 'N':
	default:
	  break;
	}
  }
  return EXIT_SUCCESS;
}

void init(void)
{
  // Global interrupts disabled
  cli();

  // Channel-B TXE#: PD2 input
  SETBIT( PORTD, PD2);
  // Channel-B RXF#: PD3 input, INT3
  SETBIT( PORTD, PD3);
  // Channel-A TXE#: PE5 input
  SETBIT( PORTE, PE5);
  // Channel-A RXF#: PE4 input, INT4
  SETBIT( PORTE, PE4);

  // SI-B : PC4 output - high
  SETBIT( DDRC, DDC4);
  SETBIT( PORTC, PC4);
  // Channel-B WR# : PC5 output - high
  SETBIT( DDRC, DDC5);
  SETBIT( PORTC, PC5);
  // Channel-B RD# : PC6 output - high
  SETBIT( DDRC, DDC6);
  SETBIT( PORTC, PC6);
  // SI-A : PF7 output - high
  SETBIT( DDRF, DDF7);
  SETBIT( PORTF, PF7);
  // Channel-A WR# : PF6 output - high
  SETBIT( DDRF, DDF6);
  SETBIT( PORTF, PF6);
  // Channel-A RD# : PF5 output - high
  SETBIT( DDRF, DDF5);
  SETBIT( PORTF, PF5);

  // LED0 : PD7 output - low
  SETBIT( DDRD, DDD7);
  // LED1 : PG0 output - low
  SETBIT( DDRG, DDG0);
  // LED2 : PG1 output - low
  SETBIT( DDRG, DDG1);

  // mem_full (data_en) : PD0 - Output - Low
  SETBIT( DDRD, DDD0);

  // test : PG4 Output - High
  SETBIT( DDRG, DDG4);
  SETBIT( PORTG, PG4);
  // reset : PG3 Output - High
  SETBIT( DDRG, DDG3);
  SETBIT( PORTG, PG3);
  // read_clk (read_data_clk) : PB6 Output - Low
  SETBIT( DDRB, DDB6);

  // read_data : PB5 Output - Low
  SETBIT( DDRB, DDB5);

  // rst_n (alt_reset) : PB4 Output - High
  SETBIT( DDRB, DDB4);
  SETBIT( PORTB, PB4);

  // start : PB3 Output - Low
  SETBIT( DDRB, DDB3);

  // clk4x : PB2 Output - Low
  SETBIT( DDRB, DDB2);

  // sell1 (fsel1) : PB0 Output - Low
  SETBIT( DDRB, DDB0);

  // sell0 (fsel0) : PE7 Output - Low
  SETBIT( DDRE, DDE7);

  // reserve2: PE6 Output - Low
//  SETBIT( DDRE, DDE6);

  // reserve1: PE3 Output - Low
//  SETBIT( DDRE, DDE3);

  // reserve0: PE2 Output - Low
//  SETBIT( DDRE, DDE2);

  // shift_rst: PF0 Output - High
  SETBIT( DDRF, DDF0);
  SETBIT( PORTF, PF0);

  // shift_clk: PF1 Output - Low
  SETBIT( DDRF, DDF1);

  // shift_data: PF2 Output - High
  SETBIT( DDRF, DDF2);
  SETBIT( PORTF, PF2);

  // hispd: PF3 Output - Low
//  SETBIT( DDRF, DDF3);

  // format: PF4 Output - Low
//  SETBIT( DDRF, DDF4);

  // start of beam extraction: PD1 input, INT1
  SETBIT( PORTD, PD1);

  // initialize timer/counter-3
  // TCNT3 = 0;
  // initialize compare value
  OCR3A = (uint16_t)VALUE; // 4881 = 1Hz

  // enable timer/counter-3 CTC mode, 1024 prescaler
  SETBITS( TCCR3B, _BV(WGM32) | _BV(CS32) | _BV(CS30));

  // enable Output Compare A Match Interrupt
  SETBIT( ETIMSK, OCIE3A);

  // Analog Comparator: Off
  SETBIT( ACSR, ACD);

  // External interrupt INT1, INT3, INT4
  // INT1, INT3, INT4 falling edge interrupt
  SETBIT( EICRA, ISC11);
  SETBIT( EICRA, ISC31);
//  SETBIT( EICRB, ISC41);

  // Reset interrupts
//  SETBIT( EIFR, INTF1);
//  SETBIT( EIFR, INTF3);
//  SETBIT( EIFR, INTF4);

  // INT1, INT3, INT4 interrupt enable
//  SETBIT( EIMSK, INT1);
  SETBIT( EIMSK, INT3);
//  SETBIT( EIMSK, INT4);

  // Global interrupts enabled
  sei();
}

void ft2232h_b_write_rom_string(PGM_P str)
{
  DDRA = 0xFF; // Port A - Output
  for (char c = pgm_read_byte(str); c; ++str, c = pgm_read_byte(str))
  {
    loop_until_bit_is_clear( PIND, PIND2); // Wait Channel B TXE# ready to read
    PORTA = c; // Write data
    CLEARBIT( PORTC, PC5); // Channel B WR# - Low level
    SETBIT( PORTC, PC5); // Channel B WR# - High level
  }
  PORTA = 0x00; // Port A - Hi-Z
  DDRA = 0x00;
}

void ft2232h_b_write_char(char c)
{
  DDRA = 0xFF; // Port A - Output
  loop_until_bit_is_clear( PIND, PIND2); // Wait Channel B TXE# ready to read
  PORTA = c; // Write data
  CLEARBIT( PORTC, PC5); // Channel B WR# - Low level
  SETBIT( PORTC, PC5); // Channel B WR# - High level
  PORTA = 0x00; // Port A - Hi-Z
  DDRA = 0x00;
}

void ft2232h_b_write_rom_string_number(uint8_t num)
{
  PGM_P str = (PGM_P)pgm_read_word(strings + num);
  ft2232h_b_write_rom_string(str);
}

void ft2232h_a_write_strobe(void)
{
  loop_until_bit_is_clear( PINE, PINE5); // Wait Channel A TXE# ready to read
  // Channel A WR# strobe
  CLEARBIT( PORTF, PF6); // Channel A WR# - Low
  SETBIT( PORTF, PF6); // Channel A WR# - High
}

void setup_integration_time(void)
{
  // ALTERA configure FSEL0 == 1, FSEL1 == 0
  SETBIT( PORTE, PE7); // FSEL0
  CLEARBIT( PORTB, PB0); // FSEL1

  // integration time value from low to high bit
  SETVAL( PORTF, PF2, integration_time & 0x01); // shift_data, input value
  SETBIT( PORTF, PF1); // shift_clk, clock high
  CLEARBIT( PORTF, PF1); // shift_clk, clock low

  SETVAL( PORTF, PF2, integration_time & 0x02); // shift_data, input value
  SETBIT( PORTF, PF1); // shift_clk, clock high
  CLEARBIT( PORTF, PF1); // shift_clk, clock low

  SETVAL( PORTF, PF2, integration_time & 0x04); // shift_data, input value
  SETBIT( PORTF, PF1); // shift_clk, clock high
  CLEARBIT( PORTF, PF1); // shift_clk, clock low

  SETVAL( PORTF, PF2, integration_time & 0x08); // shift_data, input value
  SETBIT( PORTF, PF1); // shift_clk, clock high
  CLEARBIT( PORTF, PF1); // shift_clk, clock low
}

void setup_ddc232_configuration_register(void)
{
  // ALTERA configure FSEL0 == 0, FSEL1 == 1
  CLEARBIT( PORTE, PE7); // FSEL0
  SETBIT( PORTB, PB0); // FSEL1

  // capacity value from high to low bit
  SETVAL( PORTF, PF2, chip_capacity & 0x04); // shift_data, Bit 11 (Range[2])
  SETBIT( PORTF, PF1); // shift_clk, clock high
  CLEARBIT( PORTF, PF1); // shift_clk, clock low

  SETVAL( PORTF, PF2, chip_capacity & 0x02); // shift_data, Bit 10 (Range[1])
  SETBIT( PORTF, PF1); // shift_clk, clock high
  CLEARBIT( PORTF, PF1); // shift_clk, clock low

  SETVAL( PORTF, PF2, chip_capacity & 0x01); // shift_data, Bit 9 (Range[0])
  SETBIT( PORTF, PF1); // shift_clk, clock high
  CLEARBIT( PORTF, PF1); // shift_clk, clock low

  // ADC Format 16-bit == 0
  SETVAL( PORTF, PF2, adc_format); // shift_data, Bit 8 (ADC Format)
  SETBIT( PORTF, PF1); // shift_clk, clock high
  CLEARBIT( PORTF, PF1); // shift_clk, clock low

  // DDC232CK, Version == 1
  SETBIT( PORTF, PF2); // shift_data, Bit 7 (Version) - High value
  SETBIT( PORTF, PF1); // shift_clk, clock high
  CLEARBIT( PORTF, PF1); // shift_clk, clock low

  // Clk_4x == 1
  SETBIT( PORTF, PF2); // shift_data, Bit 6 (Clk_4x) - High value
  SETBIT( PORTF, PF1); // shift_clk, clock high
  CLEARBIT( PORTF, PF1); // shift_clk, clock low

  CLEARBIT( PORTF, PF2); // shift_data, Bit 5 - Low value
  SETBIT( PORTF, PF1); // shift_clk, clock high
  CLEARBIT( PORTF, PF1); // shift_clk, clock low

  CLEARBIT( PORTF, PF2); // shift_data, Bit 4 - Low value
  SETBIT( PORTF, PF1); // shift_clk, clock high
  CLEARBIT( PORTF, PF1); // shift_clk, clock low

  CLEARBIT( PORTF, PF2); // shift_data, Bit 3 - Low value
  SETBIT( PORTF, PF1); // shift_clk, clock high
  CLEARBIT( PORTF, PF1); // shift_clk, clock low

  CLEARBIT( PORTF, PF2); // shift_data, Bit 2 - Low value
  SETBIT( PORTF, PF1); // shift_clk, clock high
  CLEARBIT( PORTF, PF1); // shift_clk, clock low

  CLEARBIT( PORTF, PF2); // shift_data, Bit 1 - Low value
  SETBIT( PORTF, PF1); // shift_clk, clock high
  CLEARBIT( PORTF, PF1); // shift_clk, clock low

  // Test mode == 0
  CLEARBIT( PORTF, PF2); // shift_data, Bit 0 (Test) - Low value
  SETBIT( PORTF, PF1); // shift_clk, clock high
  CLEARBIT( PORTF, PF1); // shift_clk, clock low
}

void setup_chips_enabled(void)
{
  // ALTERA configure FSEL0 == 1, FSEL1 == 1
  CLEARBIT( PORTE, PE7); // FSEL0
  CLEARBIT( PORTB, PB0); // FSEL1

  // Shift register reset strobe
  CLEARBIT( PORTF, PF0); // shift_rst - low
  SETBIT( PORTF, PF0); // shift_rst - high

  for (uint8_t i = 0; i < CHIPS; ++i)
  {
    SETVAL( PORTF, PF2, ((chips_enabled >> i) & 1)); // shift_data, output value
    SETBIT( PORTF, PF1); // shift_clk, clock high
    CLEARBIT( PORTF, PF1); // shift_clk, clock low
  }
}

uint8_t get_chips_enabled(void)
{
  uint8_t chips = 0;
  for (uint8_t i = 0; i < CHIPS; ++i)
  {
    chips += (chips_enabled >> i) & 1;
  }
  return chips;
}

void update_code(uint8_t cmd)
{
  if (code == cmd)
  {
    code = 'N';
  }
}
