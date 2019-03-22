/*
 * Copyright (C) 2017 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.uni.cloud.lang.speech;

import android.app.Activity;

import android.app.Service;
import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.content.SharedPreferences;
import android.os.AsyncTask;
import android.os.Binder;
import android.os.Bundle;
import android.os.Environment;
import android.os.Handler;
import android.os.IBinder;
import android.speech.tts.TextToSpeech;
import android.support.annotation.NonNull;
import android.support.annotation.Nullable;
import android.support.v4.app.ActivityCompat;
import android.support.v4.content.LocalBroadcastManager;
import android.text.TextUtils;
import android.util.Log;
import android.widget.EditText;

import com.google.auth.Credentials;
import com.google.auth.oauth2.AccessToken;
import com.google.auth.oauth2.GoogleCredentials;
import com.google.protobuf.ByteString;
import com.iflytek.cloud.ErrorCode;
import com.iflytek.cloud.InitListener;
import com.iflytek.cloud.SpeechConstant;
import com.iflytek.cloud.SpeechError;
import com.iflytek.cloud.SpeechSynthesizer;
import com.iflytek.cloud.SpeechUtility;
import com.iflytek.cloud.SynthesizerListener;
import com.iflytek.cloud.util.ResourceUtil;

import com.squareup.okhttp.Interceptor;
import com.squareup.okhttp.Request;
import com.squareup.okhttp.Response;
import com.uni.cloud.lang.R;
import com.uni.cloud.lang.misc.ByteUtil;
import com.uni.cloud.lang.misc.Option;
import com.uni.cloud.lang.xunfei_tts.TtsDemo;
import com.uni.cloud.lang.xunfei_tts.TtsSettings;
import com.uni.cloud.lang.LangApplication;

import org.json.JSONArray;
import org.json.JSONObject;

import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.net.URISyntaxException;
import java.security.KeyStore;
import java.security.SecureRandom;
import java.security.cert.CertificateFactory;
import java.security.cert.X509Certificate;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Date;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Timer;
import java.util.TimerTask;
import java.util.concurrent.TimeUnit;

import javax.net.ssl.SSLContext;
import javax.net.ssl.TrustManagerFactory;

import io.grpc.CallOptions;
import io.grpc.Channel;
import io.grpc.ClientCall;
import io.grpc.ClientInterceptor;
import io.grpc.ClientInterceptors;
import io.grpc.ManagedChannel;
import io.grpc.ManagedChannelBuilder;
import io.grpc.Metadata;
import io.grpc.MethodDescriptor;
import io.grpc.Status;
import io.grpc.StatusException;
import io.grpc.internal.DnsNameResolverProvider;
import io.grpc.okhttp.OkHttpChannelBuilder;
import io.grpc.okhttp.OkHttpChannelProvider;
import io.grpc.stub.MetadataUtils;
import io.grpc.stub.StreamObserver;
import io.grpc.uni.spos.ClientHeartReq;
import io.grpc.uni.spos.ClientHeartRes;
import io.grpc.uni.spos.ClientLoginReq;
import io.grpc.uni.spos.ClientLoginRes;
import io.grpc.uni.spos.ClientLogoutReq;
import io.grpc.uni.spos.ClientLogoutRes;
import io.grpc.uni.spos.LangGrpc;
import io.grpc.uni.spos.RecognitionConfig;
import io.grpc.uni.spos.SpeechRecognitionAlternative;

import io.grpc.uni.spos.StreamingRecTranTTsResponse;
import io.grpc.uni.spos.StreamingRecgTransTtsConfig;
import io.grpc.uni.spos.StreamingRecgTransTtsRequest;
import io.grpc.uni.spos.StreamingRecognitionConfig;
import io.grpc.uni.spos.StreamingRecognitionResult;
import io.grpc.uni.spos.StreamingRecognizeRequest;
import io.grpc.uni.spos.StreamingRecognizeResponse;

//import  com.google.cloud.texttospeech.v1beta1;


public class SpeechService extends Service {

    public interface HeartListener {
        void onHeart(boolean ret);
    }

    public interface LoginListener {
        void onLogin(boolean ret);
    }

    public interface Listener {

        /**
         * Called when a new piece of text was recognized by the Speech API.
         *
         * @param text    The text.
         * @param isFinal {@code true} when the API finished processing audio.
         */
        void onSpeechRecognized(String text, boolean isFinal);

        void onTransText(String text);

        void onTtsAudioData(byte[] audio_data);

    }

    private static final String TAG = "SpeechService";

    private static final String PREFS = "SpeechService";
    private static final String PREF_ACCESS_TOKEN_VALUE = "access_token_value";
    private static final String PREF_ACCESS_TOKEN_EXPIRATION_TIME = "access_token_expiration_time";

    /**
     * We reuse an access token if its expiration time is longer than this.
     */
    private static final int ACCESS_TOKEN_EXPIRATION_TOLERANCE = 30 * 60 * 1000; // thirty minutes
    /**
     * We refresh the current access token before it expires.
     */
    private static final int ACCESS_TOKEN_FETCH_MARGIN = 60 * 1000; // one minute

    private LangApplication mApp;

    private boolean login_ret = false;

    private boolean heart_ret = false;

    private int heart_fail_num = 0;

    private static Timer mHeartTimer = null;
    public TimerTask tHeartTask;

    public static final List<String> SCOPE =
            Collections.singletonList("https://www.googleapis.com/auth/cloud-platform");


    private final SpeechBinder mBinder = new SpeechBinder();
    private final ArrayList<Listener> mListeners = new ArrayList<>();
    private volatile AccessTokenTask mAccessTokenTask;
    private LangGrpc.LangStub mApi;
    private static Handler mHandler;

    private String  jwt_token;

    private TextToSpeech tts;

    // 语音合成对象
    private SpeechSynthesizer mTts;

    // 云端发音人列表
    private String[] cloudVoicersEntries;
    private String[] cloudVoicersValue;

    // 本地发音人列表
    private String[] localVoicersEntries;
    private String[] localVoicersValue;

    // 默认云端发音人
    public static String voicerCloud = "xiaoyan";
    // 默认本地发音人
    public static String voicerLocal = "xiaoyan";

    // 引擎类型
    private String mEngineType = SpeechConstant.TYPE_CLOUD;

    //缓冲进度
    private int mPercentForBuffering = 0;
    //播放进度
    private int mPercentForPlaying = 0;

    private SharedPreferences mSharedPreferences;

    private static final boolean stt_trans_tts_flag = true;

    private LoginListener mLoginListener;

    private HeartListener mHeartListener;

    private final StreamObserver<StreamingRecognizeResponse> mResponseObserver
            = new StreamObserver<StreamingRecognizeResponse>() {
        @Override
        public void onNext(StreamingRecognizeResponse response) {
            String text = null;
            boolean isFinal = false;
            if (response.getResultsCount() > 0) {
                final StreamingRecognitionResult result = response.getResults(0);
                isFinal = result.getIsFinal();
                if (result.getAlternativesCount() > 0) {
                    final SpeechRecognitionAlternative alternative = result.getAlternatives(0);
                    text = alternative.getTranscript();
                }
            }
            if (text != null) {
                for (Listener listener : mListeners) {
                    listener.onSpeechRecognized(text, isFinal);
                }
            }
        }

        @Override
        public void onError(Throwable t) {
            Log.e(TAG, "Error calling the API.", t);
        }

        @Override
        public void onCompleted() {
            Log.i(TAG, "API0 completed.");
        }

    };

    private final StreamObserver<StreamingRecTranTTsResponse> mNewResponseObserver
            = new StreamObserver<StreamingRecTranTTsResponse>() {
        @Override
        public void onNext(StreamingRecTranTTsResponse response) {
            Log.d(TAG, "response.getStreamingResponseCase().getNumber()=" + response.getStreamingResponseCase().getNumber());
            if (response.getStreamingResponseCase().getNumber() == 1) {
                String text = null;
                boolean isFinal = false;
                if (response.getRecg().getResultsCount() > 0) {
                    final StreamingRecognitionResult result = response.getRecg().getResults(0);
                    isFinal = result.getIsFinal();
                    if (result.getAlternativesCount() > 0) {
                        final SpeechRecognitionAlternative alternative = result.getAlternatives(0);
                        text = alternative.getTranscript();
                    }
                }
                if (text != null) {
                    for (Listener listener : mListeners) {
                        listener.onSpeechRecognized(text, isFinal);
                    }
                }
            }else if(response.getStreamingResponseCase().getNumber() == 2)
            {
                String trans_text = ByteUtil.getString(response.getTransText().toByteArray());
                Log.d(TAG, " response trans_text=" + trans_text);
                if (trans_text != null) {
                    for (Listener listener : mListeners) {
                        listener.onTransText(trans_text);
                    }
                }

            }else if(response.getStreamingResponseCase().getNumber() == 3)
            {
                Log.d(TAG, " response tts audio data!" );
                byte[] audio_data = response.getAudioData().toByteArray();
                if (audio_data != null) {
                    for (Listener listener : mListeners) {
                        listener.onTtsAudioData(audio_data);
                    }
                }
            }
        }

        @Override
        public void onError(Throwable t) {
            Log.e(TAG, "Error calling the API.", t);
        }

        @Override
        public void onCompleted() {
            Log.i(TAG, "API1 completed.");
        }

    };

//    private final StreamObserver<RecognizeResponse> mFileResponseObserver
//            = new StreamObserver<RecognizeResponse>() {
//        @Override
//        public void onNext(RecognizeResponse response) {
//            String text = null;
//            if (response.getResultsCount() > 0) {
//                final SpeechRecognitionResult result = response.getResults(0);
//                if (result.getAlternativesCount() > 0) {
//                    final SpeechRecognitionAlternative alternative = result.getAlternatives(0);
//                    text = alternative.getTranscript();
//                }
//            }
//            if (text != null) {
//                for (Listener listener : mListeners) {
//                    listener.onSpeechRecognized(text, true);
//                }
//            }
//        }

//        @Override
//        public void onError(Throwable t) {
//            Log.e(TAG, "Error calling the API.", t);
//        }
//
//        @Override
//        public void onCompleted() {
//            Log.i(TAG, "API completed.");
//        }
//
//    };

    private StreamObserver<StreamingRecognizeRequest> mRequestObserver;
    private StreamObserver<StreamingRecgTransTtsRequest> mNewRequestObserver;

    public static SpeechService from(IBinder binder) {
        return ((SpeechBinder) binder).getService();
    }

    @Override
    public void onCreate() {
        super.onCreate();

        mApp = (LangApplication) getApplication();

        mHandler = new Handler();
        fetchAccessToken();

        //patli 20180703 for  xunfei
        if (Option.FlyTek_IsOpen) {
            StringBuffer param = new StringBuffer();
            param.append("appid=" + getString(R.string.app_id));
            param.append(",");
            // 设置使用v5+
            param.append(SpeechConstant.ENGINE_MODE + "=" + SpeechConstant.MODE_MSC);
            SpeechUtility.createUtility(SpeechService.this, param.toString());

            // 初始化合成对象
            mTts = SpeechSynthesizer.createSynthesizer(this, mTtsInitListener);

            // 云端发音人名称列表
            cloudVoicersEntries = getResources().getStringArray(R.array.voicer_cloud_entries);
            cloudVoicersValue = getResources().getStringArray(R.array.voicer_cloud_values);

            // 本地发音人名称列表
            localVoicersEntries = getResources().getStringArray(R.array.voicer_local_entries);
            localVoicersValue = getResources().getStringArray(R.array.voicer_local_values);

            mSharedPreferences = getSharedPreferences(TtsSettings.PREFER_NAME, Activity.MODE_PRIVATE);
        }

        registerBoradcastReceiver();
    }

    @Override
    public void onDestroy() {
        super.onDestroy();
        mHandler.removeCallbacks(mFetchAccessTokenRunnable);
        mHandler = null;
        // Release the gRPC channel.
        if (mApi != null) {
            final ManagedChannel channel = (ManagedChannel) mApi.getChannel();
            if (channel != null && !channel.isShutdown()) {
                try {
                    channel.shutdown().awaitTermination(5, TimeUnit.SECONDS);
                } catch (InterruptedException e) {
                    Log.e(TAG, "Error shutting down the gRPC channel.", e);
                }
            }
            mApi = null;
        }

        unregisterReceiver(mBroadcastReceiver);

    }


    private void fetchAccessToken() {
        if (mAccessTokenTask != null) {
            return;
        }
        mAccessTokenTask = new AccessTokenTask();
        mAccessTokenTask.execute();
    }

    private String getDefaultLanguageCode() {
        final Locale locale = Locale.getDefault();
        final StringBuilder language = new StringBuilder(locale.getLanguage());
        final String country = locale.getCountry();
        Log.d(TAG, "country=" + country);
        if (!TextUtils.isEmpty(country)) {
            language.append("-");
            language.append(country);
        }
        Log.d(TAG, "language.toString()=" + language.toString());
        return language.toString();
    }

    @Nullable
    @Override
    public IBinder onBind(Intent intent) {
        return mBinder;
    }

    public void addListener(@NonNull Listener listener) {
        mListeners.add(listener);
    }

    public void removeListener(@NonNull Listener listener) {
        mListeners.remove(listener);
    }

    /**
     * Starts recognizing speech audio.
     *
     * @param sampleRate The sample rate of the audio.
     */
    public void startRecognizing(String lang, int sampleRate, String trans_souce, String trans_target, String tts_lang, int tts_gender, int tts_audio_code) {

        Log.w(TAG, "startRecognizing the request. lang=" + lang + "; sampleRate=" + sampleRate);
        Log.w(TAG, "startRecognizing trans_souce=" + trans_souce + "; trans_target=" + trans_target + "; tts_lang=" + tts_lang);

        if (mApi == null) {
            Log.w(TAG, "API not ready. Ignoring the request.");
            return;
        }
        // Configure the API
        if (stt_trans_tts_flag) {
            mNewRequestObserver = mApi.streamingRecTransTTs(mNewResponseObserver);
            mNewRequestObserver.onNext(StreamingRecgTransTtsRequest.newBuilder()
                    .setStreamingConfig(StreamingRecgTransTtsConfig.newBuilder()
                            .setConfig(RecognitionConfig.newBuilder()
                                    .setLanguageCode(lang)
                                    .setEncoding(RecognitionConfig.AudioEncoding.LINEAR16)
                                    .setSampleRateHertz(sampleRate)
                                    .build())
                            .setInterimResults(true)
                            .setSingleUtterance(true)
                            .setTransSoure(trans_souce)
                            .setTransTarget(trans_target)
                            .setTtsLn(tts_lang)
                            .setTtsGender(tts_gender)
                            .setTtsAudioCode(tts_audio_code)
                            .build())
                    .build());
        } else {
            mRequestObserver = mApi.streamingRecognize(mResponseObserver);
            mRequestObserver.onNext(StreamingRecognizeRequest.newBuilder()
                    .setStreamingConfig(StreamingRecognitionConfig.newBuilder()
                            .setConfig(RecognitionConfig.newBuilder()
                                    .setLanguageCode(lang)
                                    .setEncoding(RecognitionConfig.AudioEncoding.LINEAR16)
                                    .setSampleRateHertz(sampleRate)
                                    .build())
                            .setInterimResults(true)
                            .setSingleUtterance(true)
                            .build())
                    .build());
        }
    }

    /**
     * Recognizes the speech audio. This method should be called every time a chunk of byte buffer
     * is ready.
     *
     * @param data The audio data.
     * @param size The number of elements that are actually relevant in the {@code data}.
     */
    public void recognize(byte[] data, int size) {
        if (stt_trans_tts_flag) {
            Log.w(TAG, "recognize0 the audio.");
            if (mNewRequestObserver == null) {
                return;
            }
            // Call the streaming recognition API
            mNewRequestObserver.onNext(StreamingRecgTransTtsRequest.newBuilder()
                    .setAudioContent(ByteString.copyFrom(data, 0, size))
                    .build());
        } else {
            Log.w(TAG, "recognize1 the audio.");
            if (mRequestObserver == null) {
                return;
            }
            // Call the streaming recognition API
            mRequestObserver.onNext(StreamingRecognizeRequest.newBuilder()
                    .setAudioContent(ByteString.copyFrom(data, 0, size))
                    .build());
        }
    }

    /**
     * Finishes recognizing speech audio.
     */
    public void finishRecognizing() {
        if (stt_trans_tts_flag) {
            Log.w(TAG, "finishRecognizing0 the audio.");

            if (mNewRequestObserver == null) {
                return;
            }
            mNewRequestObserver.onCompleted();
            mNewRequestObserver = null;
        }else
        {
            Log.w(TAG, "finishRecognizing1 the audio.");

            if (mRequestObserver == null) {
                return;
            }
            mRequestObserver.onCompleted();
            mRequestObserver = null;
        }
    }

    /**
     * Recognize all data from the specified {@link InputStream}.
     * <p>
     * //     * @param stream The audio data.
     */
//    public void recognizeInputStream(String lang, InputStream stream) {
//        try {
//            if (mApi == null) {
//                Log.w(TAG, "API not ready. Ignoring the request.");
//                return;
//            }
//            mApi.recognize(
//                    RecognizeRequest.newBuilder()
//                            .setConfig(RecognitionConfig.newBuilder()
//                                    .setEncoding(RecognitionConfig.AudioEncoding.LINEAR16)
//                                    .setLanguageCode(lang)
//                                    .setSampleRateHertz(16000)
//                                    .build())
//                            .setAudio(RecognitionAudio.newBuilder()
//                                    .setContent(ByteString.readFrom(stream))
//                                    .build())
//                            .build(),
//                    mFileResponseObserver);
//        } catch (IOException e) {
//            Log.e(TAG, "Error loading the input", e);
//        }
//    }

    private class SpeechBinder extends Binder {

        SpeechService getService() {
            return SpeechService.this;
        }

    }

    private final Runnable mFetchAccessTokenRunnable = new Runnable() {
        @Override
        public void run() {
            fetchAccessToken();
        }
    };

    private class AccessTokenTask extends AsyncTask<Void, Void, AccessToken> {

        @Override
        protected AccessToken doInBackground(Void... voids) {
            return null;
        }

        @Override
        protected void onPostExecute(AccessToken accessToken) {
//            mAccessTokenTask = null;
            Log.d(TAG, "AccessTokenTask host=" + Option.host +";port="+Option.port);

            ManagedChannel channel;

            if(Option.Ssl_IsOpen)
            {
                try {
                    // Loading CAs from an InputStream
                    CertificateFactory cf;
                    cf = CertificateFactory.getInstance("X.509");

                    final X509Certificate server_ca;
                    InputStream cert = getResources().openRawResource(R.raw.gubstech);
                    server_ca = (X509Certificate) cf.generateCertificate(cert);
                    cert.close();

                    // Creating a KeyStore containing our trusted CAs
                    String keyStoreType = KeyStore.getDefaultType();
                    KeyStore keyStore = KeyStore.getInstance(keyStoreType);
                    keyStore.load(null, null);
                    keyStore.setCertificateEntry("ca-gubstech", server_ca);

                    SSLContext sslContext = SSLContext.getInstance("TLS");

                    TrustManagerFactory trustManagerFactory = TrustManagerFactory.getInstance(TrustManagerFactory
                            .getDefaultAlgorithm());

                    trustManagerFactory.init(keyStore);
                    sslContext.init(null, trustManagerFactory.getTrustManagers(), new SecureRandom());

                    if(Option.IsK8s_test){
                        Log.d(TAG, "AccessTokenTask ssl k8s test host=" + Option.k8s_test_host +";port="+Option.k8s_test_port);
                        channel = OkHttpChannelBuilder.forAddress(Option.k8s_test_host, Option.k8s_test_port)
                                .overrideAuthority(Option.dns_name)
                                .sslSocketFactory(sslContext.getSocketFactory())
                                .build();
                    }else {
                        Log.d(TAG, "AccessTokenTask ssl host=" + Option.host +";port="+Option.ssl_port);

                        channel = OkHttpChannelBuilder.forAddress(Option.host, Option.ssl_port)
                                .overrideAuthority(Option.dns_name)
                                .sslSocketFactory(sslContext.getSocketFactory())
                                .build();
                    }

                    mApi = LangGrpc.newStub(channel);

//                    Log.d(TAG, "AccessTokenTask add token");
//                    // create a custom header
//                    Metadata header=new Metadata();
//                    Metadata.Key<String> key =  Metadata.Key.of("Authorization", Metadata.ASCII_STRING_MARSHALLER);
//                    header.put(key, "Bearer "+"eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJ1c2VyaWQiOiJVMTU0MjA5Nzc5OCIsImV4cCI6MTU0NDY0Njc3MiwiaWF0IjoxNTQ0NjEwNzcyfQ.ZFE9dJAcbnWxGXrtUZM6zTkeXSB2dI67GwF29PF51i0");
//                    mApi = MetadataUtils.attachHeaders(mApi, header);

       //             Log.d(TAG, "AccessTokenTask ssl host=" + Option.host +";port="+Option.ssl_port);

                }catch (Exception e)
                {
                    e.printStackTrace();
                }

            }else {

                if(Option.IsK8s_test){
                    Log.d(TAG, "AccessTokenTask k8s test host=" + Option.k8s_test_host +";port="+Option.k8s_test_port);
                    channel = ManagedChannelBuilder.forAddress(Option.k8s_test_host, Option.k8s_test_port).usePlaintext(true).build();
                }else{
                    channel = ManagedChannelBuilder.forAddress(Option.host, Option.port).usePlaintext(true).build();
                }

                mApi = LangGrpc.newStub(channel);
            }

        }
    }

    public void registerBoradcastReceiver() {
        // 注册广播
        IntentFilter myIntentFilter = new IntentFilter();

        myIntentFilter.addAction("com.ut.pos.tts");

        registerReceiver(mBroadcastReceiver, myIntentFilter);
    }

    private BroadcastReceiver mBroadcastReceiver = new BroadcastReceiver() {
        @Override
        public void onReceive(Context context, Intent intent) {

            Log.d(TAG, "onReceive action=" + intent.getAction());

            String action = intent.getAction();
            if (action.equals("com.ut.pos.tts")) {

                if (Option.FlyTek_IsOpen) {
                    String text = intent.getStringExtra("com.ut.pos.tts.str");
                    String lang = intent.getStringExtra("com.ut.pos.tts.lang");
                    Log.d(TAG, "com.ut.pos.tts.str=" + text + ";lang=" + lang);
                    // 设置参数
                    if (lang.equals("pt")) {
                        setParam("xiaoyan");
                    } else if (lang.equals("gd")) {
                        setParam("xiaomei");
                    } else {
                        setParam("xiaoyan");
                    }

                    int code = mTts.startSpeaking(text, mTtsListener);
//			/**
//			 * 只保存音频不进行播放接口,调用此接口请注释startSpeaking接口
//			 * text:要合成的文本，uri:需要保存的音频全路径，listener:回调接口
//			*/
//			String path = Environment.getExternalStorageDirectory()+"/tts.pcm";
//			int code = mTts.synthesizeToUri(text, path, mTtsListener);

                    MainActivity.getMainActivity().CleanmText();  //patli 20180709

                    if (code != ErrorCode.SUCCESS) {
                        Log.d(TAG, "语音合成失败,错误码: " + code);
                    }
                }

            }
        }
    };

    /**
     * 参数设置
     *
     * @param
     * @return
     */
    private void setParam(String lang_voice) {

        Log.d(TAG, "setParam lang_voice=" + lang_voice);

        // 清空参数
        mTts.setParameter(SpeechConstant.PARAMS, null);
        //设置合成
        if (mEngineType.equals(SpeechConstant.TYPE_CLOUD)) {
            //设置使用云端引擎
            mTts.setParameter(SpeechConstant.ENGINE_TYPE, SpeechConstant.TYPE_CLOUD);
            //设置发音人
//            mTts.setParameter(SpeechConstant.VOICE_NAME,voicerCloud);
            mTts.setParameter(SpeechConstant.VOICE_NAME, lang_voice);
        } else {
            //设置使用本地引擎
            mTts.setParameter(SpeechConstant.ENGINE_TYPE, SpeechConstant.TYPE_LOCAL);
            //设置发音人资源路径
            mTts.setParameter(ResourceUtil.TTS_RES_PATH, getResourcePath());
            //设置发音人
            mTts.setParameter(SpeechConstant.VOICE_NAME, voicerLocal);
        }
        //设置合成语速
        mTts.setParameter(SpeechConstant.SPEED, mSharedPreferences.getString("speed_preference", "50"));
        //设置合成音调
        mTts.setParameter(SpeechConstant.PITCH, mSharedPreferences.getString("pitch_preference", "50"));
        //设置合成音量
        mTts.setParameter(SpeechConstant.VOLUME, mSharedPreferences.getString("volume_preference", "50"));
        //设置播放器音频流类型
        mTts.setParameter(SpeechConstant.STREAM_TYPE, mSharedPreferences.getString("stream_preference", "3"));

        // 设置播放合成音频打断音乐播放，默认为true
        mTts.setParameter(SpeechConstant.KEY_REQUEST_FOCUS, "true");

        // 设置音频保存路径，保存音频格式支持pcm、wav，设置路径为sd卡请注意WRITE_EXTERNAL_STORAGE权限
        // 注：AUDIO_FORMAT参数语记需要更新版本才能生效
        mTts.setParameter(SpeechConstant.AUDIO_FORMAT, "wav");
        mTts.setParameter(SpeechConstant.TTS_AUDIO_PATH, Environment.getExternalStorageDirectory() + "/msc/tts.wav");
    }

    //获取发音人资源路径
    private String getResourcePath() {
        StringBuffer tempBuffer = new StringBuffer();
        //合成通用资源
        tempBuffer.append(ResourceUtil.generateResourcePath(this, ResourceUtil.RESOURCE_TYPE.assets, "tts/common.jet"));
        tempBuffer.append(";");
        //发音人资源
        tempBuffer.append(ResourceUtil.generateResourcePath(this, ResourceUtil.RESOURCE_TYPE.assets, "tts/" + TtsDemo.voicerLocal + ".jet"));
        return tempBuffer.toString();
    }

    /**
     * 初始化监听。
     */
    private InitListener mTtsInitListener = new InitListener() {
        @Override
        public void onInit(int code) {
            Log.d(TAG, "InitListener init() code = " + code);
            if (code != ErrorCode.SUCCESS) {
                Log.d(TAG, "初始化失败,错误码：" + code);
            } else {
                // 初始化成功，之后可以调用startSpeaking方法
                // 注：有的开发者在onCreate方法中创建完合成对象之后马上就调用startSpeaking进行合成，
                // 正确的做法是将onCreate中的startSpeaking调用移至这里
            }
        }
    };

    /**
     * 合成回调监听。
     */
    private SynthesizerListener mTtsListener = new SynthesizerListener() {

        @Override
        public void onSpeakBegin() {
            Log.d(TAG, "开始播放");
        }

        @Override
        public void onSpeakPaused() {
            Log.d(TAG, "暂停播放");
        }

        @Override
        public void onSpeakResumed() {
            Log.d(TAG, "继续播放");
        }

        @Override
        public void onBufferProgress(int percent, int beginPos, int endPos,
                                     String info) {
            // 合成进度
            mPercentForBuffering = percent;
            Log.d(TAG, String.format(getString(R.string.tts_toast_format),
                    mPercentForBuffering, mPercentForPlaying));
        }

        @Override
        public void onSpeakProgress(int percent, int beginPos, int endPos) {
            // 播放进度
            mPercentForPlaying = percent;
            Log.d(TAG, String.format(getString(R.string.tts_toast_format),
                    mPercentForBuffering, mPercentForPlaying));
        }

        @Override
        public void onCompleted(SpeechError error) {
            if (error == null) {
                Log.d(TAG, "播放完成");
            } else if (error != null) {
                Log.d(TAG, error.getPlainDescription(true));
            }
        }

        @Override
        public void onEvent(int eventType, int arg1, int arg2, Bundle obj) {
            // 以下代码用于获取与云端的会话id，当业务出错时将会话id提供给技术支持人员，可用于查询会话日志，定位出错原因
            // 若使用本地能力，会话id为null
            //	if (SpeechEvent.EVENT_SESSION_ID == eventType) {
            //		String sid = obj.getString(SpeechEvent.KEY_EVENT_SESSION_ID);
            //		Log.d(TAG, "session id =" + sid);
            //	}
        }
    };

    public void setLoginListener(@NonNull LoginListener listener) {
        mLoginListener = listener;
    }

    public void setHeartListener(@NonNull HeartListener listener) {
        mHeartListener = listener;
    }

    public void RemoveLoginListener(@NonNull LoginListener listener) {
        listener = null;
    }

    public void RemoveHeartListener(@NonNull HeartListener listener) {
        listener = null;
    }

    public boolean Login(String id, String password) {

        if (mApi == null) {
            Log.w(TAG, "API not ready. Ignoring the request login.");
            return false;
        }

        mApp.setOwer_id(id);
        mApp.setOwer_password(password);

        ClientLoginReq loginReq = ClientLoginReq.newBuilder().setSid(id)
                .setMac(mApp.getMac())
                .setPassword(password)
                .build();

        mApi.login(loginReq, mLoginResponseObserver);

        return true;
    }

    public boolean Logout(String id) {

        if (mApi == null) {
            Log.w(TAG, "API not ready. Ignoring the request logout.");
            return false;
        }

        ClientLogoutReq logoutReq = ClientLogoutReq.newBuilder().setSid(id)
                .setMac(mApp.getMac())
                .build();

        mApi.logout(logoutReq, mLogoutResponseObserver);

//        RecvMsgReq recvReq = RecvMsgReq.newBuilder().setSid(id)
//                .setName(name)
//                .setMac(mac)
//                .build();
//
//        mApi.recvMsgStream(recvReq, mRecvMsgResObserver);

        return true;
    }

    private final StreamObserver<ClientLoginRes> mLoginResponseObserver
            = new StreamObserver<ClientLoginRes>() {
        @Override
        public void onNext(ClientLoginRes response) {
            Log.d(TAG, "login response.getRet=" + response.getRet() + ";res_str=" + response.getResStr()+";res_token="+ response.getResToken());
            boolean ret = false;
            if (response.getRet()) {
                mApp.mUsers.clear();
                try {
                    JSONArray jsonArray = new JSONArray(response.getResStr());
                    for (int i = 0; i < jsonArray.length(); i++) {
                        JSONObject jsonObject = jsonArray.getJSONObject(i);
                        String id = jsonObject.getString("id");
                        String name = jsonObject.getString("name");
                        boolean islogin = jsonObject.getBoolean("islogin");
                        boolean isonline = jsonObject.getBoolean("isonline");
                        if (!id.contentEquals(mApp.getOwer_id())) {
                            mApp.mUsers.add(new User(id, name, islogin,isonline));
                        } else {
                            mApp.setOwer_name(name);
                        }
                        Log.d(TAG, "id=" + id + ";name=" + name + ";islogin=" + islogin+ ";isonline=" + isonline);
                    }

                    Log.d(TAG, "mUsers size=" +mApp.mUsers.size());
                } catch (Exception e) {
                    e.printStackTrace();
                }

                login_ret = true;

                Log.d(TAG, "-----AccessTokenTask add token---------");
                // create a custom header
                Metadata header=new Metadata();
                Metadata.Key<String> key =  Metadata.Key.of("Authorization", Metadata.ASCII_STRING_MARSHALLER);
                header.put(key, "Bearer "+response.getResToken());
                mApi = MetadataUtils.attachHeaders(mApi, header);
            } else {
                login_ret = false;
            }


        }

        @Override
        public void onError(Throwable t) {
            Log.e(TAG, "Error calling the login API. err=", t);
        }

        @Override
        public void onCompleted() {

            mLoginListener.onLogin(login_ret);
            startHeartTimer();
            Log.i(TAG, "login API completed.");
        }

    };

    private final StreamObserver<ClientLogoutRes> mLogoutResponseObserver
            = new StreamObserver<ClientLogoutRes>() {
        @Override
        public void onNext(ClientLogoutRes response) {
            Log.d(TAG, "logout response.getRet=" + response.getRet());
        }

        @Override
        public void onError(Throwable t) {
            Log.e(TAG, "Error calling the logout API. err=", t);
        }

        @Override
        public void onCompleted() {
            //            for (Listener listener : mListeners) {
//                listener.onLogin(ret);
//            }
//            mLoginListener.onLogin(login_ret);
            Log.i(TAG, "logout API completed.");
        }

    };

    private final StreamObserver<ClientHeartRes> mHeartResponseObserver
            = new StreamObserver<ClientHeartRes>() {
        @Override
        public void onNext(ClientHeartRes response) {
            Log.d(TAG, "heart response.getRet=" + response.getRet() + ";res_str=" + response.getMsg());
            boolean ret = false;
            if (response.getRet()) {
                try {
                    JSONArray jsonArray = new JSONArray(response.getMsg());
                    for (int i = 0; i < jsonArray.length(); i++) {
                        JSONObject jsonObject = jsonArray.getJSONObject(i);
                        String id = jsonObject.getString("id");
//                        String mac = jsonObject.getString("mac");
                        boolean islogin = jsonObject.getBoolean("islogin");
                        boolean isonline = jsonObject.getBoolean("isonline");
                        boolean isrecvok = jsonObject.getBoolean("isrecvok");

                        for (int index =0; index < mApp.mUsers.size(); index++){
                            if(id.equals(mApp.mUsers.get(index).id)){
                                mApp.mUsers.get(index).setLogin(islogin);
                                mApp.mUsers.get(index).setOnline(isonline);
                                mApp.mUsers.get(index).setRecvok(isrecvok);
                            }
                        }

                        Log.d(TAG, "id=" + id + ";islogin=" + islogin + ";isonline=" + isonline);
                    }
                } catch (Exception e) {
                    e.printStackTrace();
                }
                heart_ret = true;
                heart_fail_num = 0;
            } else {
                heart_ret = false;
                heart_fail_num++;
            }


        }

        @Override
        public void onError(Throwable t) {
            Log.e(TAG, "Error calling the heart API. err=", t);
        }

        @Override
        public void onCompleted() {

            if(mHeartListener!=null) mHeartListener.onHeart(heart_ret);

            Log.i(TAG, "heart API completed.heart_ret="+ heart_ret+";heart_fail_num="+ heart_fail_num);

            if(!heart_ret&&heart_fail_num>=Option.heart_fail_max_num) {
                Login(mApp.getOwer_id(), mApp.getOwer_password());
            }
        }

    };

    public void restartHeartTimer() {
        stopHeartTimer();
        startHeartTimer();
    }

    public void startHeartTimer() {

        if(!mApp.isLogin) return;

        if(!Option.Heart_IsOpen) return;

        Log.w(TAG, "startHeartTimer.");

        if (mHeartTimer == null) {
            mHeartTimer = new Timer();
        }

        tHeartTask = new TimerTask() {
            @Override
            public void run() {

                Log.w(TAG, "heart req TimerTask  run.");
                ClientHeartReq heartReq = ClientHeartReq.newBuilder().setSid(mApp.getOwer_id())
                        .setMac(mApp.getMac())
                        .build();

                mApi.heartMsg(heartReq, mHeartResponseObserver);

            }
        };

        mHeartTimer.schedule(tHeartTask, 10*1000, Option.heart_time * 1000);
    }

    /*
     * public void stopHeartTimer() { if(mTimer != null) {
     * log("stop heart timer"); mTimer.cancel(); } }
     */
    public void stopHeartTimer() {

        if(!Option.Heart_IsOpen) return;

        if (tHeartTask != null) {
            tHeartTask.cancel();
            tHeartTask = null;
        }

        if (mHeartTimer != null) {
            mHeartTimer.cancel();
            mHeartTimer.purge();
            mHeartTimer = null;
        }

    }



}
