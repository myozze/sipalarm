/*
=================================================================================
 Name        : sipalarm.c
 Version     : 0.3

 Copyright (C) 2019 by Andreas Niggl, 2019, andreas.niggl@mail.de

 Description :
	 Tool for making voice calls over SIP/VOIP with PJSUA library

 Dependencies:
	- PJSUA API (PJSIP)

================================================================================
This tool is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version.

This tool is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.
================================================================================
*/
enum CtrlCode
{
	NIL, SOH, STX, ETX, EOT, ENQ, ACK, BEL, BS, HT, LF, VT, FF, CR, SO, SI,
	DLE, DC1, XON = DC1, DC2, DC3, XOFF = DC3, DC4, NAK, SYN, ETB, CAN, EM, SUB, ESC, FS, GS, RS, US
};

enum states
{
	INIT, SLEEP, CALL, WAIT_FOR_CONFIRM, CONFIRMED, WAIT_FOR_VTX, SPEAK, WAIT_FOR_SPEAK_FINISHED, SPEAK_FINISHED, HANGUP = 9
};

// includes
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>

#define LOG_LEVEL	5
#if defined(PJ_WINJ32)	// win32
#include "winsock2.h"
#include <pjlib.h>
#include <pjlib-util.h>
#include <pjnath.h>
#include <pjsip.h>
#include <pjsip_ua.h>
#include <pjsip_simple.h>
#include <pjsua-lib/pjsua.h>
#include <pjmedia.h>
#include <pjmedia-codec.h>
#include "pjsua.h"
#include <windows.h>
#include <tchar.h>
//#include <libloaderapi.h>
#define delay(x)	Sleep(x)
#define MAXPATH   260
#define MAXDIR    256
#define MAXFILE   256
#define MAXDRIVE	3
#define ST_WAV_FILE	"tts.wav"	// wav file
SOCKET sockfd = INVALID_SOCKET;
SERVICE_STATUS          ssStatus;       // current status of the service
SERVICE_STATUS_HANDLE   sshStatusHandle;
DWORD                   dwErr = 0;
TCHAR                   szErr[256];

char tts_file[MAXPATH];		// The service executable location
char temp_file[MAXPATH];	// The service executable location
char log_file[MAXPATH];	// The service executable location
//LPCTSTR lpszBinaryPathName = TEXT("d:\\trunk\\sipalarm\\windows\\Debug\\sipalarm.exe");		// Service display name...
//LPCTSTR lpszServiceName = TEXT("SipAlarmService");
LPTSTR GetLastErrorText(LPTSTR lpszBuf, DWORD dwSize);
BOOL ReportStatusToSCMgr(DWORD dwCurrentState, DWORD dwWin32ExitCode, DWORD dwWaitHint);
VOID AddToMessageLog(LPTSTR lpszMsg);
VOID ServiceStart(DWORD dwArgc, LPTSTR *lpszArgv);
VOID ServiceStop();
int installService(void);
void removeService();
void WINAPI ServiceMain(DWORD dwArgc, LPTSTR *lpszArgv);
TCHAR drive[MAXDRIVE];
TCHAR dir[MAXPATH];
TCHAR szServicePath[MAXPATH];
TCHAR szServiceName[MAXFILE];
LPCTSTR szServiceDisplayName = TEXT("SipAlarmService");
//TCHAR szFilename[MAXFILE];
TCHAR szWavePath[MAXPATH];
#else					// linux
#include <unistd.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <pjsua-lib/pjsua.h>
#define delay(x)	usleep(x*1000)
int sockfd;
char *tts_file = "/home/pro/tts.wav";
char *temp_file = "/home/pro/temp.wav";
char *log_file = "/home/pro/log/pjsip.log";
#endif

#define REPETITION_LIMIT 	5
#define PORT     			8888
#define MAXLINE 			1024
#define CALL_TIMEOUT		30000
#define SPEAK_TIMEOUT		30000

char sip_domain[256] = "";
char sip_user[256] = "";
char sip_password[256] = "";
char phone_number[256] = "";
char testprint[1024] = "";
char ctest[6] = "";
int test = 0;
#ifdef TEST
int debug = 1;
#else
int debug = 0;
#endif
int SipAlarmEnable = 1;

FILE * pFile;
//char *tts;
char ATCOMMAND[] = "AT";
char ATDT[] = "ATDT";
char ATVTX[] = "AT+VTX";
char ATSIP[] = "AT+SIP=";
char ATA[] = "ATA";
char ATH[] = "ATH;";

struct sockaddr_in servaddr, cliaddr;
int addrlen;
char sendbuffer[MAXLINE];
char readbuffer[MAXLINE];

// global helper vars
int call_confirmed = 0;
int media_counter = 0;
int app_exiting = 0;
int stored_digit = 0;
static int callstate = SLEEP;
static int old_callstate = SLEEP;
static int repetition = 0;
static int new_speak = 1;
static unsigned long SysTime;
static unsigned long StartTime;
static pjsua_call_id global_call_id;

// global vars for pjsua
pjsua_acc_id acc_id;
pjsua_player_id play_id = PJSUA_INVALID_ID;
pjmedia_port *play_port;

// header of helper-methods
static int create_player(pjsua_call_id);
static void log_message(char *);
static int make_sip_call();
static int register_sip(void);
static int remove_sip(void);
static void setup_sip(void);
static void create_udp(void);
static int read_udp(void);
static void write_udp(int n);
unsigned long GetSysTime();
void deleteWaveFile();

// header of callback-methods
static void on_call_media_state(pjsua_call_id);
static void on_call_state(pjsua_call_id, pjsip_event *);
static void on_dtmf_digit(pjsua_call_id call_id, int digit);
static void on_incoming_call(pjsua_acc_id acc_id, pjsua_call_id call_id, pjsip_rx_data *rdata);
static void on_media_finished(pjmedia_port *, void *);

// header of app-control-methods
static void call_exit();
static void error_exit(const char *, pj_status_t);


static void StartSipAlarm()
{
	create_udp();
	setup_sip();
	callstate = INIT;


	while (SipAlarmEnable)
	{
		int n;
		switch (callstate)
		{
		case INIT:  // warten auf Init
		case SLEEP:	// warten
			if ((n = read_udp()) > 0)
			{
				if (memcmp(ATSIP, readbuffer, strlen(ATSIP)) == 0)
				{
					//if (sscanf(readbuffer+7, "%s %s %s", sip_domain, sip_user, sip_password) == 3)
					if (sscanf(readbuffer + 7, "%255[^;];%255[^;];%255[^;];%5[^;\r]", sip_domain, sip_user, sip_password, ctest) >= 3) // %[^_]_%[^_]_%[^_]_%[^_]_%s"
					{
						test = atoi(ctest);
						sprintf(testprint, "sip='%s','%s','%s',test=%d", sip_domain, sip_user, sip_password, test);
						log_message(testprint);
						pj_log_set_level((test & 8) ? LOG_LEVEL : 0);
						remove_sip();
						deleteWaveFile();
						if (register_sip())
						{
							log_message("Register SIP Error");
							sendbuffer[0] = '4';	// ERROR
						}
						else
						{
							log_message("Register SIP OK");
							sendbuffer[0] = '0';	// OK
							callstate = SLEEP;
						}
						delay(5000);
					}
					else
					{
						log_message("ERROR!");
						sendbuffer[0] = '4';	// ERROR
					}
					sendbuffer[1] = 13;
					sendbuffer[2] = 0;
					write_udp(strlen(sendbuffer));
				}
				else if (memcmp(ATDT, readbuffer, strlen(ATDT)) == 0)
				{
					if (callstate>INIT && sscanf(readbuffer + 4, "%s", phone_number) == 1)
					{
						StartTime = GetSysTime();
						callstate = CALL;
						break;
					}
					else
					{
						log_message("ERROR!");
						sendbuffer[0] = '4';	// ERROR
						sendbuffer[1] = 13;
						sendbuffer[2] = 0;
						write_udp(strlen(sendbuffer));
					}
				}
				else if (memcmp(ATVTX, readbuffer, strlen(ATVTX)) == 0)
				{
					log_message("NOT CONNECTED");
					sendbuffer[0] = DLE;
					sendbuffer[1] = 's';
					write_udp(2);
				}
				else if (memcmp(ATA, readbuffer, strlen(ATA)) == 0)
				{
					log_message("ANWSER COMMAND...");
					pjsua_call_answer(global_call_id, 200, NULL, NULL);
					sendbuffer[0] = '0';	// OK
					sendbuffer[1] = 13;
					sendbuffer[2] = 0;
					write_udp(strlen(sendbuffer));
					//callstate = 1;
				}
				else if (memcmp(ATH, readbuffer, strlen(ATH)) == 0)
				{
					log_message("ANWSER COMMAND...");
					test = atoi(readbuffer + 4);	// ATH;x
					pj_log_set_level((test & 8) ? LOG_LEVEL : 0);
					sendbuffer[0] = '0';	// OK
					sendbuffer[1] = 13;
					sendbuffer[2] = 0;
					write_udp(strlen(sendbuffer));
					//callstate = ?;
				}
				else if (memcmp(ATCOMMAND, readbuffer, strlen(ATCOMMAND)) == 0)
				{
					//log_message("OK!");
					sendbuffer[0] = (callstate == INIT) ? '4' : '0';	// ERROR/OK
					sendbuffer[1] = 13;
					sendbuffer[2] = 0;
					write_udp(strlen(sendbuffer));
				}
				else memset(readbuffer, 0, sizeof(readbuffer));

			}
			break;
		case CALL:
			sprintf(testprint, "call %s", phone_number);
			log_message(testprint);
			if (make_sip_call() == PJ_SUCCESS)
			{
				log_message("SUCESS!");
				callstate = WAIT_FOR_CONFIRM;
			}
			else
			{
				log_message("ERROR!");
				sendbuffer[0] = '4';	// ERROR
				sendbuffer[1] = 13;
				sendbuffer[2] = 0;
				write_udp(strlen(sendbuffer));
				callstate = SLEEP;
			}
			break;
		case WAIT_FOR_CONFIRM:	// Call gestartet // wait for confirm
			delay(1);
			if ((GetSysTime() - StartTime) > CALL_TIMEOUT)
			{
				sendbuffer[0] = '4';	// ERROR
				sendbuffer[1] = 13;
				sendbuffer[2] = 0;
				write_udp(strlen(sendbuffer));
				log_message("CALL TIMEOUT!");
				callstate = HANGUP;
			}
			break;
		case CONFIRMED:	// Call confirmed
			sendbuffer[0] = '1';	// CONNECT
			sendbuffer[1] = 13;
			sendbuffer[2] = 0;
			write_udp(strlen(sendbuffer));
			log_message("CONFIRMED!");
			callstate = WAIT_FOR_VTX;
			break;
		case WAIT_FOR_VTX:	// wait for vtx command
			if ((n = read_udp()) > 0)
			{
				if (memcmp(ATVTX, readbuffer, strlen(ATVTX)) == 0)
				{
					stored_digit = 0;	// init
				  #if defined(PJ_WINJ32)	// win32
					CopyFile((LPCTSTR)tts_file, (LPCTSTR)temp_file, FALSE);
				  #else
					system("cp -f tts.wav temp.wav");
				  #endif
					pFile = fopen(temp_file, "r");
					if (pFile != NULL)	// wav file exists?
					{
						fclose(pFile);
						callstate = SPEAK;
					}
					else
						log_message("wav file not found");
				}
				else if (memcmp(ATCOMMAND, readbuffer, strlen(ATCOMMAND)) == 0 && strchr(readbuffer, 'H'))
				{
					log_message("HANGUP COMMAND...");
					sendbuffer[0] = '0';	// OK
					sendbuffer[1] = 13;
					sendbuffer[2] = 0;
					write_udp(strlen(sendbuffer));
					callstate = HANGUP;
				}
				else
				{
					sprintf(testprint, "get data: %s", readbuffer);
					log_message(testprint);
				}
			}
			break;
		case SPEAK:	// speak
			delay(1);
			log_message("SPEAK...");
			create_player(global_call_id);	//ANDI
			pjmedia_wav_player_port_set_pos(play_port, 0);	//ANDI?
			new_speak = 1;
			StartTime = GetSysTime();
			callstate = WAIT_FOR_SPEAK_FINISHED;
			break;
		case WAIT_FOR_SPEAK_FINISHED:	// wait for speak finished
			delay(1);
			if ((GetSysTime() - StartTime) > SPEAK_TIMEOUT)
			{
				log_message("SPEAK TIMEOUT");
				callstate = SPEAK_FINISHED;
			}
			break;
		case SPEAK_FINISHED: // speak finished
			log_message("FINISHED!");
			if (play_id != -1)
			{
				log_message("Destroy player ... ");
				pjsua_player_destroy(play_id);
				play_id = -1;
			}
			sendbuffer[0] = DLE;
			sendbuffer[1] = ACK;
			write_udp(2);
			if (stored_digit)
			{
				sendbuffer[0] = DLE;
				sendbuffer[1] = stored_digit;
				write_udp(2);
			}
			new_speak = 0;
			//deleteWaveFile();
			callstate = WAIT_FOR_VTX;
			break;
		case HANGUP: // Hangup
			log_message("HANG UP!");
			if (play_id != -1)
			{
				log_message("Destroy player ... ");
				pjsua_player_destroy(play_id);
				play_id = -1;
			}
			pjsua_call_hangup_all();
			callstate = SLEEP;
			break;
		}
		//synthesize_speech(tts_file);
		// initiate call
		//make_sip_call();

		delay(10);

		if (callstate != old_callstate)
		{
			sprintf(testprint, "callstate: %d", callstate);
			log_message(testprint);
		}
		old_callstate = callstate;

	}

	// exit app
	call_exit();
	return;
}

// main application
int main(int argc, char *argv[])
{
#if defined(PJ_WINJ32)	// win32
	printf("Start SipAlarm...");
	GetModuleFileName(NULL, szServicePath, MAXPATH);
	_tsplitpath(szServicePath, drive, dir, szServiceName, 0);
#ifdef TEST
	sprintf(tts_file, "d:\\trunk\\pro10.1\\Mip\\Mip\\MIP_NT\\Debug\\tts.wav");
	sprintf(log_file, "d:\\trunk\\pro10.1\\Mip\\Mip\\MIP_NT\\Debug\\log\\pjsip.log");
#else
	_tmakepath(tts_file, drive, dir, "tts", "wav");
	_tmakepath(log_file, drive, dir, "log\\pjsip", "log");
#endif
	_tmakepath(temp_file, drive, dir, "temp", "wav");
	if (argc > 1)
	{
		if (memcmp(argv[1], "-d", 2) == 0)
		{
			debug = 1;
			StartSipAlarm();
		}
		else if (memcmp(argv[1], "-run", 4) == 0)
			StartSipAlarm();
		else if (memcmp(argv[1], "-install", 8) == 0)
		{
			installService();
			exit(0);
		}
		else if (memcmp(argv[1], "-remove", 8) == 0)
		{
			removeService();
			exit(0);
		}
		else
			goto dispatch;
		exit(0);
	}
dispatch:
	{
		// this is just to be friendly
		printf("%s -install  to install the service\n", szServiceName);
		printf("%s -remove   to remove the service\n", szServiceName);
		printf("%s -run      to run as a console app\n", szServiceName);
		printf("%s -d        to run as a console app for debugging pjlib\n", szServiceName);
		printf("\nStartServiceCtrlDispatcher being called.\n");
		printf("This may take several seconds.  Please wait.\n");

		//TCHAR szFilename[300];
		//strcpy(szFilename, szServiceName);

		SERVICE_TABLE_ENTRY dispatchTable[] =
		{
			{szServiceName, (LPSERVICE_MAIN_FUNCTION)ServiceMain },
			{ NULL, NULL }
		};
		if (!StartServiceCtrlDispatcher(dispatchTable))
			AddToMessageLog(TEXT("StartServiceCtrlDispatcher failed."));
	}
#else			// linux
	if (argc > 1)
		if (memcmp(argv[1], "-d", 2) == 0)
			debug = 1;
	StartSipAlarm();
#endif
}

// ************** PJLIB FUNCTIONS **************************************************

// helper for logging messages to console (disabled if silent mode is active)
static void log_message(char *message)
{
	if (test & 8)
	{
		PJ_LOG(4, ("sipalarm.c", message));
		//fprintf(stderr, "SIP: ");
		//fprintf(stderr, message);
	}
}

// helper for setting up sip library pjsua
static void setup_sip(void)
{
	pj_status_t status;

	log_message("Setting up pjsua ... ");

	// create pjsua
	status = pjsua_create();
	if (status != PJ_SUCCESS) error_exit("Error in pjsua_create()", status);

	// configure pjsua
	pjsua_config cfg;
	pjsua_media_config   media_cfg;
	pjsua_config_default(&cfg);

	// enable just 1 simultaneous call
	cfg.max_calls = 1;

	// callback configuration
	cfg.cb.on_call_media_state = &on_call_media_state;
	cfg.cb.on_call_state = &on_call_state;
	cfg.cb.on_dtmf_digit = &on_dtmf_digit;
	cfg.cb.on_incoming_call = &on_incoming_call;

	//NEU
	pjsua_media_config_default(&media_cfg);

	media_cfg.enable_ice = PJ_FALSE;
	media_cfg.no_vad = PJ_TRUE;
	media_cfg.ec_tail_len = 0;	//PJSUA_DEFAULT_EC_TAIL_LEN;
	media_cfg.clock_rate = 8000;
	media_cfg.channel_count = 1;


	// logging configuration
	pjsua_logging_config log_cfg;
	pjsua_logging_config_default(&log_cfg);
	//log_cfg.console_level = debug;

	// initialize pjsua
	log_cfg.decor |= PJ_LOG_HAS_CR;
	log_cfg.log_filename = pj_str(log_file);
	log_cfg.level = (test & 8) ? LOG_LEVEL : 0;
	log_cfg.console_level = debug ? 5 : 0;
	status = pjsua_init(&cfg, &log_cfg, &media_cfg);
	if (status != PJ_SUCCESS) error_exit("Error in pjsua_init()", status);

		// initialization is done, start pjsua
	status = pjsua_start();
	if (status != PJ_SUCCESS) error_exit("Error starting pjsua", status);

	//NEU

	unsigned count = PJMEDIA_CODEC_MGR_MAX_CODECS;
	pjsua_codec_info codec_info[PJMEDIA_CODEC_MGR_MAX_CODECS];
	if (pjsua_enum_codecs(codec_info, &count) == PJ_SUCCESS)
		for (unsigned i = 0; i < count; i++)
			pjsua_codec_set_priority(&codec_info[i].codec_id, PJMEDIA_CODEC_PRIO_DISABLED);



	pj_str_t codec_id;
	//pjmedia_codec_param param;
	int i = PJMEDIA_CODEC_PRIO_NORMAL;


	codec_id = pj_str("PCMA/8000");
	pjsua_codec_set_priority(&codec_id, i--);
	codec_id = pj_str("PCMU/8000/1");
	pjsua_codec_set_priority(&codec_id, i--);
	//codec_id = pj_str("G722/16000/1");
	//pjsua_codec_set_priority(&codec_id, i--);
	//codec_id = pj_str("telephone-event");
	//pjsua_codec_set_priority(&codec_id, i--);


	// add udp transport
	pjsua_transport_config udpcfg;
	pjsua_transport_config_default(&udpcfg);
	udpcfg.port = 0;// 5060;
	status = pjsua_transport_create(PJSIP_TRANSPORT_UDP, &udpcfg, NULL);
	if (status != PJ_SUCCESS) error_exit("Error creating transport", status);

	// disable sound - use null sound device
	status = pjsua_set_null_snd_dev();
	if (status != PJ_SUCCESS) error_exit("Error disabling audio", status);

	log_message("Done.");
}

// helper for creating and registering sip-account
static int register_sip(void)
{
	pj_status_t status;

	log_message("Registering account ... ");

	// prepare account configuration
	pjsua_acc_config cfg;
	pjsua_acc_config_default(&cfg);

	// build sip-user-url
	char sip_user_url[256];
	sprintf(sip_user_url, "sip:%s@%s", sip_user, sip_domain);

	// build sip-provder-url
	char sip_provider_url[256];
	sprintf(sip_provider_url, "sip:%s", sip_domain);

	// create and define account
	cfg.id = pj_str(sip_user_url);
	cfg.reg_uri = pj_str(sip_provider_url);
	cfg.cred_count = 1;
	cfg.cred_info[0].realm = pj_str("*");//sip_domain);
	cfg.cred_info[0].scheme = pj_str("digest");
	cfg.cred_info[0].username = pj_str(sip_user);
	cfg.cred_info[0].data_type = PJSIP_CRED_DATA_PLAIN_PASSWD;
	cfg.cred_info[0].data = pj_str(sip_password);

	// add account
	status = pjsua_acc_add(&cfg, PJ_TRUE, &acc_id);

	if (status != PJ_SUCCESS)
	{
		log_message("Error acc_add.");
		return 1;
	}

	//cfg.
	//cfg.lock_codec = 9;
	//pjsua_acc_modify(acc_id, &cfg);

	if (status != PJ_SUCCESS)
	{
		log_message("Error acc modify.");
		return 1;
	}
	/*
	pj_str_t codec_id;
	codec_id = pj_str("G722/8000");
	status = pjsua_codec_set_priority(&codec_id, (pj_uint8_t)PJMEDIA_CODEC_PRIO_NORMAL);

	if (status != PJ_SUCCESS)
	{
		log_message("Error codec_set_priority.");
		return 1;
	}
	*/
	log_message("Done.");
	return 0;
}

// helper for creating and registering sip-account
static int remove_sip(void)
{
	//pj_status_t status;

	log_message("Remove account ... ");

	if (pjsua_acc_is_valid(acc_id))
	{

		//        pjsua_acc_info info;
		//        pjsua_acc_get_info(_sip_acc_id, &info);
		//
		//        if (info.has_registration){
		pj_status_t statusDelete = pjsua_acc_del(acc_id);
		if (statusDelete != PJ_SUCCESS)
		{
			log_message("Error removing new account");
			return 1;
		}
		//        }
	}

	log_message("Done.");
	return 0;
}

// helper for making calls over sip-account
static int make_sip_call()
{
	pj_status_t status;

	if (pjsua_acc_is_valid(acc_id))
		log_message("Starting call with valid Account ...");
	else
		log_message("Invalid Account ...");

	// build target sip-url
	char sip_target_url[40];
	sprintf(sip_target_url, "sip:%s@%s", phone_number, sip_domain);

	// NEU
	pjsua_call_setting call_setting;
	pjsua_call_setting_default(&call_setting);
	call_setting.flag = 0;
	call_setting.vid_cnt = 0;

	pjsua_msg_data msg_data;
	pjsua_msg_data_init(&msg_data);

	// start call with sip-url
	pj_str_t uri = pj_str(sip_target_url);
	status = pjsua_call_make_call(acc_id, &uri, &call_setting, NULL, &msg_data, NULL);
	//status = pjsua_call_dial_dtmf(acc_id, &uri, 0, NULL, NULL, NULL);
	return status;	//if (status != PJ_SUCCESS) error_exit("Error making call", status);

}

// helper for creating call-media-player
static int create_player(pjsua_call_id call_id)
{
	// get call infos
	pjsua_call_info ci;
	pjsua_call_get_info(call_id, &ci);

	pj_str_t name;
	pj_status_t status = PJ_ENOTFOUND;

	log_message("Creating player ... ");

#if 0	// Amazon mp3
	char speech_command[] = "lame --decode /home/pro/tts.mp3 /home/pro/tts.wav";
	system(speech_command);
#endif

	// create player for playback media
	status = pjsua_player_create(pj_cstr(&name, temp_file), PJMEDIA_FILE_NO_LOOP, &play_id);
	if (status != PJ_SUCCESS) //error_exit("Error playing sound-playback", status);
	{
		log_message("Error");
		return 1;
	}

	// connect active call to media player
	pjsua_conf_connect(pjsua_player_get_conf_port(play_id), ci.conf_slot);

	// get media port (play_port) from play_id
	status = pjsua_player_get_port(play_id, &play_port);
	if (status != PJ_SUCCESS)
	{
		log_message("Error");
		return 1;
	}

	// register media finished callback
	status = pjmedia_wav_player_set_eof_cb2(play_port, NULL, &on_media_finished);
	if (status != PJ_SUCCESS)
	{
		log_message("Error");
		return 1;
	}
	log_message("DONE");
	return 0;
}

// handler for call-media-state-change-events
static void on_call_media_state(pjsua_call_id call_id)
{
	// get call infos
	pjsua_call_info ci;
	pjsua_call_get_info(call_id, &ci);
	global_call_id = call_id;
	//pj_status_t status = PJ_ENOTFOUND;

	sprintf(testprint, "on_call_media_state: %d", ci.media_status);
	log_message(testprint);

	// check state if call is established/active
	if (ci.media_status == PJSUA_CALL_MEDIA_ACTIVE/* && callstate<2*/)
	{
		log_message("Call media activated.");
	}
}

// handler for call-state-change-events
static void on_call_state(pjsua_call_id call_id, pjsip_event *e)
{
	// get call infos
	pjsua_call_info ci;
	pjsua_call_get_info(call_id, &ci);

	// prevent warning about unused argument e
	PJ_UNUSED_ARG(e);

	sprintf(testprint, "on_call_state: %d", ci.state);
	log_message(testprint);

	// check call state
	if (ci.state == PJSIP_INV_STATE_CONFIRMED)
	{
		log_message("Call confirmed.");
		callstate = CONFIRMED;
	}
	else if (ci.state == PJSIP_INV_STATE_DISCONNECTED)
	{
		/* Wiederholen bringt nix!
		if (callstate == WAIT_FOR_CONFIRM && ((GetSysTime() - StartTime) < CALL_TIMEOUT))
		{
			log_message("Call disconnected. Retry ...");
			delay(3000);
			callstate = CALL;
		}
		else*/
		{
			log_message("Call disconnected. Hangup");
			sendbuffer[0] = DLE;
			sendbuffer[1] = 's';
			write_udp(2);
			callstate = HANGUP;
			//pjsua_call_hangup_all();
		}
	}
}

// handler for incoming calls
static void on_incoming_call(pjsua_acc_id acc_id, pjsua_call_id call_id, pjsip_rx_data *rdata)
{
	pjsua_call_info ci;
	pjsua_call_get_info(call_id, &ci);
	//global_call_id = call_id;
	global_call_id = call_id;

	PJ_UNUSED_ARG(acc_id);
	PJ_UNUSED_ARG(rdata);

	//(int)ci.remote_info.slen,	ci.remote_info.ptr));

	log_message("Incoming call");

	/* Automatically answer incoming calls with 200/OK */
	//pjsua_call_answer(call_id, 200, NULL, NULL);

	sendbuffer[0] = '2';
	sendbuffer[1] = 13;
	sendbuffer[2] = 0;
	write_udp(3);
}

// handler for call-state-change-events
static void on_dtmf_digit(pjsua_call_id call_id, int digit)
{
	// get call infos
	pjsua_call_info ci;
	pjsua_call_get_info(call_id, &ci);

	// check call state
	sprintf(testprint, "   --- DTMF digit %d !!!!!!!!!!!!", digit);
	log_message(testprint);
	sendbuffer[0] = DLE;
	sendbuffer[1] = digit;
	write_udp(2);
	stored_digit = digit;	// Fuer Menue zwischenspeichern
}

// handler for media-finished-events
static void on_media_finished(pjmedia_port *media_port, void *user_data)
{
	PJ_UNUSED_ARG(media_port);
	PJ_UNUSED_ARG(user_data);

	sprintf(testprint, "on_media_finished");
	log_message(testprint);

	if (new_speak && callstate == WAIT_FOR_SPEAK_FINISHED)
	{
		callstate = SPEAK_FINISHED;
	}
}

// clean application exit
static void call_exit()
{
	if (!app_exiting)
	{
		app_exiting = 1;
		log_message("Stopping application ... ");

		// check if player is active and stop them
		if (play_id != -1)
		{
			log_message("Destroy player ... ");
			pjsua_player_destroy(play_id);
			play_id = -1;
		}
		// hangup open calls and stop pjsua
		pjsua_call_hangup_all();
		pjsua_destroy();

		log_message("Done.");

		exit(0);
	}
}

// display error and exit application
static void error_exit(const char *title, pj_status_t status)
{
	if (!app_exiting)
	{
		app_exiting = 1;

		pjsua_perror("SIP Call", title, status);

		// check if player is active and stop them
		if (play_id != -1)
		{
			log_message("Destroy player ... ");
			pjsua_player_destroy(play_id);
			play_id = -1;
		}
		// hangup open calls and stop pjsua
		pjsua_call_hangup_all();
		pjsua_destroy();

		exit(1);
	}
}


// ************** WIN32/LINUX FUNCTIONS **************************************************

#if defined(PJ_WINJ32)	// win32

void deleteWaveFile()
{
	DeleteFile(tts_file);
}

unsigned long GetSysTime()
{
	return SysTime = GetTickCount();
}

static void create_udp(void)
{
	int iResult;
	WSADATA wsaData;
	iResult = WSAStartup(MAKEWORD(2, 2), &wsaData);
	if (iResult != NO_ERROR) {
		wprintf(L"WSAStartup failed with error: %d\n", iResult);
		exit(EXIT_FAILURE);
	}
	// Creating socket file descriptor
	if ((sockfd = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP)) == INVALID_SOCKET) {
		perror("socket creation failed");
		exit(EXIT_FAILURE);

	}
	memset(&servaddr, 0, sizeof(servaddr));

	// Filling server information
	servaddr.sin_family = AF_INET; // IPv4
	servaddr.sin_addr.S_un.S_addr = INADDR_ANY; //ADDR_ANY;
	servaddr.sin_port = htons(PORT);

	// Bind the socket with the server address
	if (bind(sockfd, (const struct sockaddr *)&servaddr, sizeof(servaddr)) < 0)
	{
		perror("bind failed");
		exit(1);
	}
	u_long data = 1;
	if (ioctlsocket(sockfd, FIONBIO, &data) == -1)	// Windows
	{
		perror("SetNonblocking failed\n");
		exit(1);
	}
}

static int read_udp(void)
{
	addrlen = sizeof(cliaddr);
	int n = recvfrom(sockfd, (char *)readbuffer, MAXLINE,
		0, (struct sockaddr *) &cliaddr, &addrlen);
	if (n > 0)
		return n;
	else if (n == SOCKET_ERROR)
	{
		//printf("read error %d\n", WSAGetLastError());
		return n;
	}
	return 0;
}

static void write_udp(int n)
{
	sendto(sockfd, (const char *)sendbuffer, n,
		0, (const struct sockaddr *) &cliaddr,
		addrlen);
}

//
//  FUNCTION: service_ctrl
//
//  PURPOSE: This function is called by the SCM whenever
//           ControlService() is called on this service.
//
//  PARAMETERS:
//    dwCtrlCode - type of control requested
//
//  RETURN VALUE:
//    none
//
//  COMMENTS:
//
VOID WINAPI ServiceCtrl(DWORD dwCtrlCode)
{
	// Handle the requested control code.
	//
	switch (dwCtrlCode)
	{
		// Stop the service.
		//
	case SERVICE_CONTROL_STOP:
	case SERVICE_CONTROL_SHUTDOWN:
		ssStatus.dwCurrentState = SERVICE_STOP_PENDING;
		ServiceStop();
		break;

		// Update the service status.
		//
	case SERVICE_CONTROL_INTERROGATE:
		break;

		// invalid control code
		//
	default:
		break;

	}

	ReportStatusToSCMgr(ssStatus.dwCurrentState, NO_ERROR, 0);

}

//
//  FUNCTION: ControlHandler ( DWORD dwCtrlType )
//
//  PURPOSE: Handled console control events
//
//  PARAMETERS:
//    dwCtrlType - type of control event
//
//  RETURN VALUE:
//    True - handled
//    False - unhandled
//
//  COMMENTS:
//
BOOL WINAPI ControlHandler(DWORD dwCtrlType)
{
	switch (dwCtrlType)
	{
	case CTRL_BREAK_EVENT:  // use Ctrl+C or Ctrl+Break to simulate
	case CTRL_C_EVENT:      // SERVICE_CONTROL_STOP in debug mode
		//_tprintf(TEXT("Stopping %s.\n"), TEXT(SZSERVICEDISPLAYNAME));
		ServiceStop();
		return TRUE;

	case CTRL_CLOSE_EVENT:
	case CTRL_SHUTDOWN_EVENT:
		ServiceStop();
		/* 			int fd = open("c:\service.log", O_WRONLY|O_CREAT, S_IWRITE); */
		/* 			write(fd, "SERVICE_STOP\n", sizeof("SERVICE_STOP\n"));       */
		/* 			close(fd);                                                   */
		Sleep(10000);
		return TRUE;
	}
	return FALSE;
}

//
//  FUNCTION: service_main
//
//  PURPOSE: To perform actual initialization of the service
//
//  PARAMETERS:
//    dwArgc   - number of command line arguments
//    lpszArgv - array of command line arguments
//
//  RETURN VALUE:
//    none
//
//  COMMENTS:
//    This routine performs the service initialization and then calls
//    the user defined ServiceStart() routine to perform majority
//    of the work.
//
void WINAPI ServiceMain(DWORD dwArgc, LPTSTR *lpszArgv)
{

	// register our service control handler:
	//
	sshStatusHandle = RegisterServiceCtrlHandler(szServiceName, ServiceCtrl);

	if (!sshStatusHandle)
		goto cleanup;

	// SERVICE_STATUS members that don't change in example
	//
	ssStatus.dwServiceType = SERVICE_WIN32_OWN_PROCESS;
	ssStatus.dwServiceSpecificExitCode = 0;


	// report the status to the service control manager.
	//
	if (!ReportStatusToSCMgr(
		SERVICE_START_PENDING, // service state
		NO_ERROR,              // exit code
		30000))                 // wait hint
		goto cleanup;

	SetConsoleCtrlHandler(ControlHandler, TRUE);

	ServiceStart(dwArgc, lpszArgv);

cleanup:

	// try to report the stopped status to the service control manager.
	//
	if (sshStatusHandle)
		(VOID)ReportStatusToSCMgr(
			SERVICE_STOPPED,
			dwErr,
			0);

	return;
}

//
//  FUNCTION: GetLastErrorText
//
//  PURPOSE: copies error message text to string
//
//  PARAMETERS:
//    lpszBuf - destination buffer
//    dwSize - size of buffer
//
//  RETURN VALUE:
//    destination buffer
//
//  COMMENTS:
//
LPTSTR GetLastErrorText(LPTSTR lpszBuf, DWORD dwSize)
{
	DWORD dwRet;
	LPTSTR lpszTemp = NULL;

	dwRet = FormatMessage(FORMAT_MESSAGE_ALLOCATE_BUFFER | FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_ARGUMENT_ARRAY,
		NULL,
		GetLastError(),
		LANG_NEUTRAL,
		(LPTSTR)&lpszTemp,
		0,
		NULL);

	// supplied buffer is not long enough
	if (!dwRet || ((long)dwSize < (long)dwRet + 14))
		lpszBuf[0] = TEXT('\0');
	else
	{
		lpszTemp[lstrlen(lpszTemp) - 2] = TEXT('\0');  //remove cr and newline character
		sprintf(lpszBuf, TEXT("%s (0x%x)"), lpszTemp, GetLastError());
	}

	if (lpszTemp)
		LocalFree((HLOCAL)lpszTemp);

	return lpszBuf;
}

//
//  FUNCTION: ReportStatusToSCMgr()
//
//  PURPOSE: Sets the current status of the service and
//           reports it to the Service Control Manager
//
//  PARAMETERS:
//    dwCurrentState - the state of the service
//    dwWin32ExitCode - error code to report
//    dwWaitHint - worst case estimate to next checkpoint
//
//  RETURN VALUE:
//    TRUE  - success
//    FALSE - failure
//
//  COMMENTS:
//
BOOL ReportStatusToSCMgr(DWORD dwCurrentState,
	DWORD dwWin32ExitCode,
	DWORD dwWaitHint)
{
	static DWORD dwCheckPoint = 1;
	BOOL fResult = TRUE;


	if (1) // when debugging we don't report to the SCM
	{
		if (dwCurrentState == SERVICE_START_PENDING)
			ssStatus.dwControlsAccepted = 0;
		else
			ssStatus.dwControlsAccepted = SERVICE_ACCEPT_STOP;

		ssStatus.dwCurrentState = dwCurrentState;
		ssStatus.dwWin32ExitCode = dwWin32ExitCode;
		ssStatus.dwWaitHint = dwWaitHint;

		if ((dwCurrentState == SERVICE_RUNNING) ||
			(dwCurrentState == SERVICE_STOPPED))
			ssStatus.dwCheckPoint = 0;
		else
			ssStatus.dwCheckPoint = dwCheckPoint++;


		// Report the status of the service to the service control manager.
		//
		if ((fResult = SetServiceStatus(sshStatusHandle, &ssStatus)) == 0) {
			AddToMessageLog(TEXT("SetServiceStatus"));
		}
	}
	return fResult;
}

//
//  FUNCTION: AddToMessageLog(LPTSTR lpszMsg)
//
//  PURPOSE: Allows any thread to log an error message
//
//  PARAMETERS:
//    lpszMsg - text for message
//
//  RETURN VALUE:
//    none
//
//  COMMENTS:
//
VOID AddToMessageLog(LPTSTR lpszMsg)
{
	TCHAR   szMsg[256];
	HANDLE  hEventSource;
	LPTSTR  lpszStrings[2];


	if (1)
	{
		dwErr = GetLastError();

		// Use event logging to log the error.
		//
		hEventSource = RegisterEventSource(NULL, szServiceName);

		sprintf(szMsg, TEXT("%s error: %d"), szServiceName, dwErr);
		lpszStrings[0] = szMsg;
		lpszStrings[1] = lpszMsg;

		if (hEventSource != NULL) {
			ReportEvent(hEventSource, // handle of event source
				EVENTLOG_ERROR_TYPE,  // event type
				0,                    // event category
				0,                    // event ID
				NULL,                 // current user's SID
				2,                    // strings in lpszStrings
				0,                    // no bytes of raw data
				(LPCTSTR*)lpszStrings,          // array of error strings
				NULL);  // no raw data

			(VOID)DeregisterEventSource(hEventSource);
		}
	}
}


// Install Service
int installService(void)
{
	SC_HANDLE schSCManager, schService;

	// Open a handle to the SC Manager database...
	schSCManager = OpenSCManager(
		NULL, // local machine
		NULL, // SERVICES_ACTIVE_DATABASE database is opened by default
		SC_MANAGER_ALL_ACCESS); // full access rights

	if (NULL == schSCManager)
		printf("OpenSCManager() failed, error: %d.\n", GetLastError());
	else
		printf("OpenSCManager() looks OK.\n");

	// Create/install service...
	// If the function succeeds, the return value is a handle to the service. If the function fails, the return value is NULL.
	schService = CreateService(
		schSCManager, // SCManager database
		szServiceName, // name of service
		szServiceDisplayName, // service name to display
		SERVICE_ALL_ACCESS, // desired access
		SERVICE_WIN32_OWN_PROCESS, // service type
		SERVICE_AUTO_START, // start type
		SERVICE_ERROR_NORMAL, // error control type
		szServicePath, // service's binary
		NULL, // no load ordering group
		NULL, // no tag identifier
		NULL, // no dependencies, for real telnet there are dependencies lor
		NULL, // LocalSystem account
		NULL); // no password

	if (schService == NULL)
	{
		printf("CreateService() failed, error: %ld\n", GetLastError());
		return FALSE;
	}
	else
	{
		printf("CreateService() for %s looks OK.\n", szServiceName);
		if (CloseServiceHandle(schService) == 0)
			printf("CloseServiceHandle() failed, Error: %d.\n", GetLastError());
		else
			printf("CloseServiceHandle() is OK.\n");
		return 0;
	}

}

// Remove Service
void removeService()
{
	SC_HANDLE   schService;
	SC_HANDLE   schSCManager;
	// Registry Subkey

	schSCManager = OpenSCManager(
		NULL,                   // machine (NULL == local)
		NULL,                   // database (NULL == default)
		SC_MANAGER_ALL_ACCESS   // access required
	);
	if (schSCManager)
	{
		schService = OpenService(schSCManager, szServiceName, SERVICE_ALL_ACCESS);

		if (schService)
		{
			// try to stop the service
			if (ControlService(schService, SERVICE_CONTROL_STOP, &ssStatus))
			{
				printf(TEXT("Stopping %s."), szServiceName);
				Sleep(1000);

				while (QueryServiceStatus(schService, &ssStatus))
				{
					if (ssStatus.dwCurrentState == SERVICE_STOP_PENDING)
					{
						printf(TEXT("."));
						Sleep(1000);
					}
					else
						break;
				}

				if (ssStatus.dwCurrentState == SERVICE_STOPPED)
					printf(TEXT("\n%s stopped.\n"), szServiceName);
				else
					printf(TEXT("\n%s failed to stop.\n"), szServiceName);

			}

			// now remove the service
			if (DeleteService(schService))
				printf(TEXT("%s removed.\n"), szServiceName);
			else
				printf(TEXT("DeleteService failed - %s\n"), GetLastErrorText(szErr, 256));


			CloseServiceHandle(schService);
		}
		else
			printf(TEXT("OpenService %s failed - %s\n"), szServiceName, GetLastErrorText(szErr, 256));

		CloseServiceHandle(schSCManager);
	}
	else
		printf(TEXT("OpenSCManager failed - %s\n"), GetLastErrorText(szErr, 256));
}

void ServiceStart(DWORD dwArgc, LPTSTR *lpszArgv)
{
	// Service initialization
	//
	// report the status to the service control manager.
	if (!ReportStatusToSCMgr(
		SERVICE_START_PENDING, // service state
		NO_ERROR,              // exit code
		30000))                 // wait hint
		goto cleanup;

	// report the status to the service control manager.
	if (!ReportStatusToSCMgr(
		SERVICE_RUNNING,       // service state
		NO_ERROR,              // exit code
		0))                    // wait hint
		goto cleanup;

	// End of initialization
	//
	// Service is now running, perform work until shutdown
	StartSipAlarm();

cleanup:
	;
}

void ServiceStop()
{
	SipAlarmEnable = 0;
	CoUninitialize();
}



#else			// linux

void deleteWaveFile()
{
	remove(tts_file);
}

unsigned long GetSysTime()
{
	struct timeval t1;
	gettimeofday(&t1, NULL);
	return SysTime = t1.tv_sec * 1000 + t1.tv_usec / 1000;
}

static void create_udp(void)
{
	// Creating socket file descriptor
	if ((sockfd = socket(AF_INET, SOCK_DGRAM, 0)) < 0) {
		perror("socket creation failed");
		exit(EXIT_FAILURE);
	}
	memset(&servaddr, 0, sizeof(servaddr));

	// Filling server information
	servaddr.sin_family = AF_INET; // IPv4
	servaddr.sin_addr.s_addr = INADDR_ANY;
	servaddr.sin_port = htons(PORT);

	// Bind the socket with the server address
	if (bind(sockfd, (const struct sockaddr *)&servaddr, sizeof(servaddr)) < 0)
	{
		perror("bind failed");
		exit(1);
	}
}

static int read_udp(void)
{
	return recvfrom(sockfd, (char *)readbuffer, MAXLINE,
		MSG_DONTWAIT, (struct sockaddr *) &cliaddr,
		&addrlen);
}

static void write_udp(int n)
{
	sendto(sockfd, (const char *)sendbuffer, n,
		MSG_CONFIRM, (const struct sockaddr *) &cliaddr,
		addrlen);
}

#endif
