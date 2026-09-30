// ==UserScript==
// @name         レイズ Comiru専用モニター 8.7.3
// @namespace    https://ray-school.jp/
// @version      8.7.4
// @description  レイズ Comiru座席管理 常設モニター + ReaLTE面談連携
// @updateURL     https://raw.githubusercontent.com/kaonorenn/rays-comiru-monitor/main/ray-comiru-monitor.user.js
// @downloadURL   https://raw.githubusercontent.com/kaonorenn/rays-comiru-monitor/main/ray-comiru-monitor.user.js
// @match        https://comiru.jp/ray-school/seat/index*
// @match        https://comiru.jp/ray-school/*
// @match        https://comiru.jp/ray-school_ekinan/*
// @match        https://realte.site/*
// @grant        GM_xmlhttpRequest
// @grant        GM_setValue
// @grant        GM_getValue
// @connect      script.google.com
// @connect      script.googleusercontent.com
// @connect      drive.google.com
// ==/UserScript==

(function () {
  'use strict';

  const VERSION = '8.7.4';

  /*
    v7.8 URL ROUTING
    座席管理だけRAYSモニター化。
    生徒一覧はComiru標準画面のままURL収集だけ。
    生徒詳細・その他の画面では完全に停止。
  */
  const RAY_PATH = location.pathname;

  /*
    v8.6
    Comiru校舎スラッグ
      本校   : ray-school
      駅南校 : ray-school_ekinan
  */
  const COMIRU_SCHOOL_MATCH =
    RAY_PATH.match(
      /^\/(ray-school(?:_ekinan)?)(?:\/|$)/
    );

  const COMIRU_SCHOOL_SLUG =
    COMIRU_SCHOOL_MATCH
      ? COMIRU_SCHOOL_MATCH[1]
      : 'ray-school';

  const IS_EKINAN_SCHOOL =
    COMIRU_SCHOOL_SLUG ===
    'ray-school_ekinan';

  const IS_REALTE_PAGE =
    location.hostname === 'realte.site';

  const IS_RAY_SEAT_PAGE =
    location.hostname === 'comiru.jp' &&
    /^\/ray-school(?:_ekinan)?\/seat(?:\/index)?\/?$/.test(RAY_PATH);

  const IS_RAY_STUDENT_LIST_PAGE =
    location.hostname === 'comiru.jp' &&
    /^\/ray-school(?:_ekinan)?\/students\/?$/.test(RAY_PATH);

  if (
    !IS_REALTE_PAGE &&
    !IS_RAY_SEAT_PAGE &&
    !IS_RAY_STUDENT_LIST_PAGE
  ) {
    return;
  }

  const API_BASE_URL =
    'https://script.google.com/macros/s/AKfycbyEQB4_eFOEOnOVceoby6vpADCfAil0gYOwlRc0MMULvq12OmE2DaUYKwGqS5t0XqHWxw/exec';

  const API_URL =
    API_BASE_URL + '?api=monitor';

  const SETTINGS_URL =
    'https://docs.google.com/spreadsheets/d/1nZnkRdxEyz3x7l6wpbth698IVwBtTo6gkPRnoi7Wl5s/edit';

  const LOGO_URL =
    'https://drive.google.com/thumbnail?id=1JwxThhAY8ekmTPbTCmYgRUQidKFCtALN&sz=w1000';

  const HEADER_HEIGHT = 170;
  const SIDEBAR_WIDTH = 360;

  const MAX_ENTRANCE = 6;
  const MAX_EVENTS = 6;

  /*
    標語・COUNTDOWN・イベント
    1分ごとにAPIを再取得
  */
  const DATA_REFRESH_MS = 60 * 1000;

  /*
    v6.1
    Comiruページ全体の再読み込み

    5分ごと
  */
  const COMIRU_RELOAD_MS = 5 * 60 * 1000;

  /*
    DOM上の座席情報確認
    ＋現在時間帯への追従

    10秒ごと
  */
  const DOM_CAPTURE_MS = 10 * 1000;

  /*
    手動で別時間を選んだ場合
    5分後に現在時刻へ戻る
  */
  const MANUAL_RETURN_MS = 5 * 60 * 1000;

  /*
    スタッフミーティング時間は除外
  */
  const EXCLUDED_TIMES = new Set([
    '18:50-19:05'
  ]);

  let manualStart = null;
  let manualUntil = 0;

  let seatCache = new Map();

  let scanning = false;
  let customMode = true;

  /*
    v7.1
    ダッシュボードAPIから取得する生徒ラベル情報
  */
  let firstLessonItems = [];
  let newStudentItems = [];

  /*
    v7.3
    Comiru生徒詳細・成績キャッシュ
  */
  const studentDetailCache =
    new Map();

  const studentScoreCache =
    new Map();

  /*
    v7.5
    Comiruの「生徒一覧」から
    氏名 -> /student/S_xxxxx の対応を作る。
  */
  let comiruStudentDirectoryPromise =
    null;


  // =====================================================
  // v8.0 ReaLTE INTERVIEW CACHE
  // =====================================================

  const REALTE_CACHE_KEY =
    'RAYS_REALTE_STUDENT_CACHE_V80';

  const REALTE_AI_SUMMARY_CACHE_KEY =
    'RAYS_REALTE_AI_SUMMARY_CACHE_V84';

  const realteAiPending =
    new Set();

  const REALTE_CACHE_DAYS = 365;

  function normalizeCrossSystemStudentName(v) {
    return String(v || '')
      .normalize('NFKC')
      .replace(/[（(][^）)]*[）)]/g, '')
      .replace(/[\s　]/g, '')
      .replace(/さん$/g, '')
      .toLowerCase();
  }

  function realteDateCutoff() {
    const d = new Date();

    d.setHours(0, 0, 0, 0);
    d.setFullYear(
      d.getFullYear() - 1
    );

    return d;
  }

  function realteDateValue(v) {
    const m =
      String(v || '').match(
        /^(\d{4})-(\d{1,2})-(\d{1,2})/
      );

    if (!m) {
      return null;
    }

    return new Date(
      Number(m[1]),
      Number(m[2]) - 1,
      Number(m[3])
    );
  }

  function buildRealteCache(store) {
    const students =
      store?.state?.students?.students;

    if (!Array.isArray(students)) {
      return null;
    }

    const scholae =
      Array.isArray(
        store?.state?.scholae?.scholae
      )
        ? store.state.scholae.scholae
        : [];

    const users =
      Array.isArray(
        store?.state?.users?.users
      )
        ? store.state.users.users
        : [];

    const schoolMap =
      new Map(
        scholae
          .filter(x => x?.key)
          .map(
            x => [
              String(x.key),
              String(x.name || '')
            ]
          )
      );

    const userMap =
      new Map(
        users
          .filter(x => x?.key)
          .map(
            x => [
              String(x.key),
              String(
                x.name ||
                [
                  x.sei,
                  x.mei
                ]
                  .filter(Boolean)
                  .join(' ') ||
                ''
              )
            ]
          )
      );

    const cutoff =
      realteDateCutoff();

    const byName = {};

    students
      .filter(
        student =>
          Number(student?.status) === 6
      )
      .forEach(student => {
        const normalizedName =
          normalizeCrossSystemStudentName(
            student?.name
          );

        if (!normalizedName) {
          return;
        }

        const interviews =
          (Array.isArray(student?.events)
            ? student.events
            : []
          )
            .filter(event => {
              if (
                Number(event?.type) !== 2 &&
                Number(event?.type) !== 3
              ) {
                return false;
              }

              const date =
                realteDateValue(
                  event?.date1
                );

              const memo =
                String(
                  event?.memo || ''
                ).trim();

              return (
                date &&
                date >= cutoff &&
                memo
              );
            })
            .sort(
              (a, b) =>
                String(b.date1 || '')
                  .localeCompare(
                    String(a.date1 || '')
                  )
            )
            .map(event => ({
              date:
                String(
                  event.date1 || ''
                ),
              type:
                Number(event.type) === 2
                  ? '生徒面談'
                  : '保護者面談',
              memo:
                String(
                  event.memo || ''
                ).trim(),
              staff:
                userMap.get(
                  String(
                    event.charge || ''
                  )
                ) || ''
            }));

        const characteristics =
          (Array.isArray(
            student?.characteristics
          )
            ? student.characteristics
            : []
          )
            .map(item => ({
              type:
                String(
                  item?.type || ''
                ),
              comment:
                String(
                  item?.comment || ''
                ).trim()
            }))
            .filter(
              item =>
                item.comment
            );

        byName[normalizedName] = {
          name:
            String(
              student?.name || ''
            ),
          school:
            schoolMap.get(
              String(
                student?.school || ''
              )
            ) || '',
          grade:
            String(
              student?.grade ?? ''
            ),
          characteristics,
          interviews
        };
      });

    return {
      version:
        VERSION,
      savedAt:
        Date.now(),
      savedAtText:
        new Date()
          .toISOString(),
      studentCount:
        Object.keys(byName).length,
      byName
    };
  }

  function saveRealteCacheFromStore(store) {
    const cache =
      buildRealteCache(store);

    if (
      !cache ||
      !cache.studentCount
    ) {
      return false;
    }

    GM_setValue(
      REALTE_CACHE_KEY,
      cache
    );

    console.log(
      `[RAYS v${VERSION}] ReaLTE連携キャッシュ保存: ${cache.studentCount}名`
    );

    return true;
  }

  function findRealteVueStore() {
    const app =
      document.querySelector(
        '#app'
      );

    return (
      app?.__vue__?.$store ||
      null
    );
  }

  function startRealteCacheSync() {
    let attempts = 0;

    const trySave = () => {
      attempts++;

      const store =
        findRealteVueStore();

      const students =
        store?.state?.students?.students;

      if (
        store &&
        Array.isArray(students) &&
        students.length
      ) {
        saveRealteCacheFromStore(
          store
        );

        return true;
      }

      return false;
    };

    if (trySave()) {
      setInterval(
        () => {
          const store =
            findRealteVueStore();

          if (store) {
            saveRealteCacheFromStore(
              store
            );
          }
        },
        5 * 60 * 1000
      );

      return;
    }

    const timer =
      setInterval(
        () => {
          if (
            trySave() ||
            attempts >= 30
          ) {
            clearInterval(
              timer
            );

            if (
              attempts >= 30
            ) {
              console.warn(
                `[RAYS v${VERSION}] ReaLTEの生徒データを確認できませんでした`
              );
            }
          }
        },
        1000
      );
  }

  function testRealteMatchesOnComiruStudentList() {
    const cache =
      loadRealteCache();

    if (
      !cache ||
      !cache.byName
    ) {
      console.warn(
        `[RAYS v${VERSION}] ReaLTEキャッシュがありません。先にReaLTEを開いてください。`
      );
      return;
    }

    const links =
      [
        ...document.querySelectorAll(
          'a[href*="/student/S_"]'
        )
      ];

    const seen =
      new Set();

    const rows =
      links
        .map(link => {
          const name =
            clean(
              link.textContent
            );

          const key =
            normalizeCrossSystemStudentName(
              name
            );

          return {
            name,
            key,
            matched:
              !!cache.byName[key]
          };
        })
        .filter(item => {
          if (
            !item.name ||
            !item.key ||
            seen.has(item.key)
          ) {
            return false;
          }

          seen.add(
            item.key
          );

          return true;
        });

    const matched =
      rows.filter(
        x => x.matched
      ).length;

    const unmatchedRows =
      rows.filter(
        x => !x.matched
      );

    console.log(
      `[RAYS v${VERSION}] ReaLTE照合確認: Comiru ${rows.length}名 / 一致 ${matched}名 / 不一致 ${unmatchedRows.length}名`
    );

    if (
      unmatchedRows.length
    ) {
      console.log(
        `[RAYS v${VERSION}] ReaLTE不一致（Comiru側氏名）:`,
        unmatchedRows.map(
          x => x.name
        )
      );
    }
  }

  function loadRealteCache() {
    try {
      const cache =
        GM_getValue(
          REALTE_CACHE_KEY,
          null
        );

      return (
        cache &&
        typeof cache === 'object'
      )
        ? cache
        : null;
    } catch (error) {
      console.warn(
        `[RAYS v${VERSION}] ReaLTEキャッシュ読込失敗`,
        error
      );

      return null;
    }
  }

  function getRealteStudent(
    studentName
  ) {
    const cache =
      loadRealteCache();

    if (
      !cache ||
      !cache.byName
    ) {
      return {
        cache: null,
        student: null
      };
    }

    const key =
      normalizeCrossSystemStudentName(
        studentName
      );

    return {
      cache,
      student:
        cache.byName[key] ||
        null
    };
  }

  function formatRealteCacheTime(
    savedAt
  ) {
    if (!savedAt) {
      return '';
    }

    const d =
      new Date(savedAt);

    if (
      Number.isNaN(
        d.getTime()
      )
    ) {
      return '';
    }

    return (
      `${d.getMonth() + 1}/` +
      `${d.getDate()} ` +
      `${String(d.getHours()).padStart(2, '0')}:` +
      `${String(d.getMinutes()).padStart(2, '0')}`
    );
  }

  function summarizeRealteInterviews(interviews) {
    const source =
      (interviews || [])
        .slice(0, 6)
        .map(
          x => String(x?.memo || '')
        )
        .filter(Boolean)
        .join('\n');

    if (!source) {
      return {
        issues: [],
        cautions: [],
        next: []
      };
    }

    const sentences =
      source
        .replace(/\r/g, '')
        .split(
          /(?:\n+|(?<=[。！？!?]))/
        )
        .map(
          x => clean(x)
        )
        .filter(
          x =>
            x.length >= 4
        );

    const pick = (
      words,
      max = 3
    ) => {
      const result = [];

      for (
        const sentence of sentences
      ) {
        if (
          !words.some(
            word =>
              sentence.includes(word)
          )
        ) {
          continue;
        }

        const short =
          sentence.length > 110
            ? sentence.slice(0, 107) + '…'
            : sentence;

        if (
          !result.includes(short)
        ) {
          result.push(short);
        }

        if (
          result.length >= max
        ) {
          break;
        }
      }

      return result;
    };

    return {
      issues:
        pick([
          '苦手',
          '課題',
          'できない',
          '出来ない',
          '弱い',
          '不足',
          '遅れ',
          '不安',
          '心配',
          'ミス',
          '点数',
          '成績',
          '理解',
          '集中',
          '宿題',
          '勉強',
          '学習'
        ]),
      cautions:
        pick([
          '注意',
          '指導',
          '声かけ',
          '声掛け',
          'フォロー',
          '配慮',
          '確認',
          '復習',
          '宿題',
          '進め',
          'ペース',
          'モチベ',
          'やる気',
          '集中',
          '質問',
          '自習'
        ]),
      next:
        pick([
          '次回',
          '今後',
          '次',
          '予定',
          '目標',
          '確認',
          '検討',
          '相談',
          '受験',
          'テスト',
          '模試',
          '英検',
          '漢検',
          '進路',
          '志望',
          '面談'
        ])
    };
  }

  function realteSummarySourceHash(
    student
  ) {
    const text =
      JSON.stringify({
        interviews:
          (student?.interviews || [])
            .slice(0, 6)
            .map(
              x => ({
                date:
                  String(x?.date || ''),
                type:
                  String(x?.type || ''),
                memo:
                  String(x?.memo || '')
              })
            ),
        characteristics:
          (student?.characteristics || [])
            .slice(0, 6)
            .map(
              x =>
                String(
                  x?.comment || ''
                )
            )
      });

    let hash =
      2166136261;

    for (
      let i = 0;
      i < text.length;
      i++
    ) {
      hash ^=
        text.charCodeAt(i);

      hash =
        Math.imul(
          hash,
          16777619
        );
    }

    return (
      hash >>> 0
    ).toString(16);
  }


  function readRealteAiSummaryCache() {
    try {
      const value =
        GM_getValue(
          REALTE_AI_SUMMARY_CACHE_KEY,
          {}
        );

      return (
        value &&
        typeof value === 'object'
      )
        ? value
        : {};

    } catch (error) {
      console.warn(
        `[RAYS v${VERSION}] AI要約キャッシュ読込失敗`,
        error
      );
      return {};
    }
  }


  function getRealteAiSummary(
    student
  ) {
    if (!student) {
      return null;
    }

    const key =
      normalizeCrossSystemStudentName(
        student.name || ''
      );

    if (!key) {
      return null;
    }

    const cache =
      readRealteAiSummaryCache();

    const item =
      cache[key];

    if (
      !item ||
      item.sourceHash !==
        realteSummarySourceHash(
          student
        ) ||
      !item.summary
    ) {
      return null;
    }

    return item.summary;
  }


  function requestRealteAiSummary(
    student,
    card,
    cardToken
  ) {
    if (
      !student ||
      !(student.interviews || [])
        .length
    ) {
      return;
    }

    const key =
      normalizeCrossSystemStudentName(
        student.name || ''
      );

    if (!key) {
      return;
    }

    const sourceHash =
      realteSummarySourceHash(
        student
      );

    const existing =
      getRealteAiSummary(
        student
      );

    if (existing) {
      return;
    }

    const pendingKey =
      `${key}:${sourceHash}`;

    if (
      realteAiPending.has(
        pendingKey
      )
    ) {
      return;
    }

    realteAiPending.add(
      pendingKey
    );

    GM_xmlhttpRequest({
      method:
        'POST',

      url:
        API_BASE_URL,

      headers: {
        'Content-Type':
          'application/json'
      },

      data:
        JSON.stringify({
          type:
            'geminiInterviewSummary',

          version:
            VERSION,

          interviews:
            (student.interviews || [])
              .slice(0, 6)
              .map(
                item => ({
                  date:
                    String(
                      item?.date || ''
                    ),
                  type:
                    String(
                      item?.type || ''
                    ),
                  memo:
                    String(
                      item?.memo || ''
                    )
                })
              ),

          characteristics:
            (student.characteristics || [])
              .slice(0, 6)
              .map(
                item => ({
                  comment:
                    String(
                      item?.comment || ''
                    )
                })
              )
        }),

      onload(res) {
        realteAiPending.delete(
          pendingKey
        );

        try {
          const data =
            JSON.parse(
              res.responseText ||
              '{}'
            );

          if (
            !data.ok ||
            !data.summary
          ) {
            console.error(
              `[RAYS v${VERSION}] Gemini面談要約エラー`,
              data
            );
            return;
          }

          const cache =
            readRealteAiSummaryCache();

          cache[key] = {
            sourceHash:
              sourceHash,
            savedAt:
              new Date()
                .toISOString(),
            summary:
              data.summary
          };

          GM_setValue(
            REALTE_AI_SUMMARY_CACHE_KEY,
            cache
          );

          if (
            card &&
            card.dataset
              .rayToken ===
              cardToken
          ) {
            const block =
              card.querySelector(
                '.ray-realte-block'
              );

            if (block) {
              block.innerHTML =
                realteCardHtml(
                  student.name
                );
            }
          }

        } catch (error) {
          console.error(
            `[RAYS v${VERSION}] Gemini面談要約応答解析エラー`,
            error,
            res.responseText
          );
        }
      },

      onerror(error) {
        realteAiPending.delete(
          pendingKey
        );

        console.error(
          `[RAYS v${VERSION}] Gemini面談要約通信エラー`,
          error
        );
      }
    });
  }


  function ensureRealteAiSummaryForCard(
    studentName,
    card,
    cardToken
  ) {
    const found =
      getRealteStudent(
        studentName
      );

    if (
      !found.student ||
      !(found.student.interviews || [])
        .length
    ) {
      return;
    }

    requestRealteAiSummary(
      found.student,
      card,
      cardToken
    );
  }


  function summaryLinesHtml(
    title,
    lines
  ) {
    if (
      !Array.isArray(lines) ||
      !lines.length
    ) {
      return '';
    }

    return `
      <div class="ray-card-summary-block">
        <div class="ray-card-summary-title">
          ${esc(title)}
        </div>
        ${lines
          .map(
            line => `
              <div class="ray-card-summary-line">
                ・${esc(line)}
              </div>
            `
          )
          .join('')}
      </div>
    `;
  }

  function realteCardHtml(
    studentName
  ) {
    const found =
      getRealteStudent(
        studentName
      );

    if (!found.cache) {
      return `
        <div class="ray-card-section">
          <div class="ray-card-section-title">
            ReaLTE 面談情報
          </div>
          <div class="ray-card-value">
            ReaLTEキャッシュ未作成です。ReaLTEを一度開いてください。
          </div>
        </div>
      `;
    }

    if (!found.student) {
      return `
        <div class="ray-card-section">
          <div class="ray-card-section-title">
            ReaLTE 面談情報
          </div>
          <div class="ray-card-value">
            ReaLTE在籍生との氏名一致なし
          </div>
          <div class="ray-card-source">
            ReaLTE更新 ${esc(
              formatRealteCacheTime(
                found.cache.savedAt
              )
            )}
          </div>
        </div>
      `;
    }

    const student =
      found.student;

    const characteristics =
      (student.characteristics || [])
        .slice(0, 6);

    const interviews =
      (student.interviews || [])
        .slice(0, 3);

    return `
      <div class="ray-card-section">
        <div class="ray-card-section-title">
          ReaLTE
        </div>

        ${
          student.school
            ? `
              <div class="ray-card-row">
                <div class="ray-card-label">
                  学校
                </div>
                <div class="ray-card-value">
                  ${esc(student.school)}
                </div>
              </div>
            `
            : ''
        }

        ${
          student.grade
            ? `
              <div class="ray-card-row">
                <div class="ray-card-label">
                  学年
                </div>
                <div class="ray-card-value">
                  ${esc(student.grade)}
                </div>
              </div>
            `
            : ''
        }

        ${
          characteristics.length
            ? `
              <div class="ray-card-section">
                <div class="ray-card-section-title">
                  個性・注意事項
                </div>
                ${characteristics
                  .map(
                    item => `
                      <div class="ray-card-note">
                        ${esc(item.comment)}
                      </div>
                    `
                  )
                  .join('')}
              </div>
            `
            : ''
        }

        <div class="ray-card-section">
          <div class="ray-card-section-title">
            ${
              getRealteAiSummary(
                student
              )
                ? 'AI面談要点'
                : '面談要点（AI生成中）'
            }
          </div>

          ${
            interviews.length
              ? (() => {
                  const aiSummary =
                    getRealteAiSummary(
                      student
                    );

                  const summary =
                    aiSummary ||
                    summarizeRealteInterviews(
                      student.interviews
                    );

                  const summaryHtml = [
                    summaryLinesHtml(
                      '現在の課題',
                      summary.issues
                    ),
                    summaryLinesHtml(
                      '指導上の注意',
                      summary.cautions
                    ),
                    summaryLinesHtml(
                      '次回確認事項',
                      summary.next
                    )
                  ]
                    .filter(Boolean)
                    .join('');

                  return `
                    ${
                      summaryHtml
                        ? `
                          <div class="ray-card-summary">
                            ${summaryHtml}
                          </div>
                        `
                        : `
                          <div class="ray-card-value">
                            要点候補なし
                          </div>
                        `
                    }

                    <details class="ray-card-details">
                      <summary>
                        面談原文を表示
                        （直近${interviews.length}件／1年${student.interviews.length}件）
                      </summary>

                      ${interviews
                        .map(
                          interview => `
                            <div class="ray-card-note">
                              <div>
                                <strong>
                                  ${esc(interview.date)}
                                  ${esc(interview.type)}
                                </strong>
                                ${
                                  interview.staff
                                    ? ` ／ ${esc(interview.staff)}`
                                    : ''
                                }
                              </div>
                              <div>
                                ${esc(interview.memo)}
                              </div>
                            </div>
                          `
                        )
                        .join('')}
                    </details>
                  `;
                })()
              : `
                  <div class="ray-card-value">
                    直近1年の面談メモなし
                  </div>
                `
          }
        </div>

        <div class="ray-card-source">
          ReaLTE更新 ${esc(
            formatRealteCacheTime(
              found.cache.savedAt
            )
          )}
        </div>
      </div>
    `;
  }


  // =====================================================
  // UTIL
  // =====================================================

  function esc(v) {
    return String(v ?? '')
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#039;');
  }

  function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  function clean(v) {
    return String(v || '')
      .replace(/\s+/g, ' ')
      .trim();
  }

  // =====================================================
  // v7.1 NEW / FIRST LESSON BADGES
  // =====================================================

  function normalizeStudentName(v) {
    return clean(v)
      .normalize('NFKC')
      .replace(/[（(][^）)]*[）)]/g, '')
      .replace(/[\s　]/g, '')
      .replace(/さん$/g, '');
  }

  function itemTextForStudentMatch(item) {
    if (typeof item === 'string') {
      return item;
    }

    if (!item) {
      return '';
    }

    return [
      item.name,
      item.title,
      item.text,
      item.content
    ]
      .filter(Boolean)
      .join(' ');
  }

  function itemMatchesStudent(item, studentName) {
    const name =
      normalizeStudentName(
        studentName
      );

    if (!name) {
      return false;
    }

    const text =
      normalizeStudentName(
        itemTextForStudentMatch(
          item
        )
      );

    if (!text) {
      return false;
    }

    return (
      text === name ||
      text.includes(name) ||
      name.includes(text)
    );
  }

  function getStudentEntryBadge(studentName) {
    const isFirst =
      firstLessonItems.some(
        item =>
          itemMatchesStudent(
            item,
            studentName
          )
      );

    if (isFirst) {
      return '初回';
    }

    const isNew =
      newStudentItems.some(
        item =>
          itemMatchesStudent(
            item,
            studentName
          )
      );

    if (isNew) {
      return '新規';
    }

    return '';
  }

  function timeToMinutes(v) {
    const m = String(v).match(/^(\d{1,2}):(\d{2})$/);

    if (!m) return null;

    return Number(m[1]) * 60 + Number(m[2]);
  }

  function extractTime(text) {
    const m = String(text || '').match(
      /(\d{1,2}:\d{2})\s*[-～〜]\s*(\d{1,2}:\d{2})/
    );

    if (!m) return null;

    return {
      label: `${m[1]}-${m[2]}`,
      startText: m[1],
      endText: m[2],
      start: timeToMinutes(m[1]),
      end: timeToMinutes(m[2])
    };
  }

  function nowMinutes() {
    const d = new Date();

    return (
      d.getHours() * 60 +
      d.getMinutes()
    );
  }

  function cleanup() {
    [
      'ray-header',
      'ray-sidebar',
      'ray-monitor',
      'ray-style',
      'ray-return'
    ].forEach(id => {
      document.getElementById(id)?.remove();
    });
  }


  // =====================================================
  // MANUAL / AUTO TIME
  // =====================================================

  function setManualTime(start) {
    manualStart = Number(start);

    manualUntil =
      Date.now() +
      MANUAL_RETURN_MS;
  }

  function returnToAutoTime() {
    manualStart = null;
    manualUntil = 0;
  }

  function checkManualTimeout() {
    if (
      manualStart !== null &&
      manualUntil > 0 &&
      Date.now() >= manualUntil
    ) {
      returnToAutoTime();
    }
  }


  // =====================================================
  // SCHOOL LEVEL
  // =====================================================

  function getSchoolLevel(name) {
    const v = String(name || '');

    if (/[（(]小[1-6][）)]/.test(v)) {
      return 'elementary';
    }

    if (/[（(]中[1-3][）)]/.test(v)) {
      return 'junior';
    }

    if (/[（(]高[1-3][）)]/.test(v)) {
      return 'high';
    }

    return 'other';
  }


  // =====================================================
  // CSS
  // =====================================================

  function addCSS() {
    const style = document.createElement('style');

    style.id = 'ray-style';

    style.textContent = `
      :root {
        --ray-header:${HEADER_HEIGHT}px;
        --ray-side:${SIDEBAR_WIDTH}px;
      }

      html,
      body {
        min-height:100%!important;
      }

      body {
        padding-top:var(--ray-header)!important;
        padding-left:var(--ray-side)!important;
        box-sizing:border-box!important;
      }

      /*
        v6.5
        Comiru標準画面ではRAYS独自UIを完全退避。
        Comiru本来の画面をウィンドウ全面で使う。
      */
      body.ray-standard-mode {
        padding-top:0!important;
        padding-left:0!important;
      }

      body.ray-standard-mode #ray-header,
      body.ray-standard-mode #ray-sidebar,
      body.ray-standard-mode #ray-monitor {
        display:none!important;
      }

      /* ================= HEADER ================= */

      #ray-header {
        position:fixed;
        z-index:2147483646;
        left:0;
        right:0;
        top:0;
        height:var(--ray-header);

        display:flex;

        background:
          linear-gradient(
            135deg,
            #071b38,
            #0b2d57 58%,
            #103d70
          );

        color:#fff;

        box-shadow:
          0 2px 10px rgba(0,0,0,.25);

        font-family:
          "Noto Sans JP",
          "Yu Gothic",
          Meiryo,
          sans-serif;
      }

      #ray-logo {
        width:var(--ray-side);
        min-width:var(--ray-side);

        background:#fff;

        display:flex;
        align-items:center;
        justify-content:center;

        box-sizing:border-box;

        padding:10px 18px;
      }

      #ray-logo img {
        max-width:100%;
        max-height:145px;
        object-fit:contain;
      }

      #ray-head-main {
        flex:1;
        position:relative;

        padding:18px 30px;

        display:flex;
        justify-content:center;
        flex-direction:column;
      }

      #ray-slogan-label {
        font-size:19px;
        font-weight:900;
        color:#a9cdf2;
        margin-bottom:4px;
      }

      #ray-slogan {
        font-size:34px;
        line-height:1.15;
        font-weight:900;
      }

      #ray-notices {
        display:none !important;
      }

      .ray-notice {
        background:rgba(255,255,255,.13);
        padding:4px 10px;
        border-radius:5px;
        font-size:14px;
        font-weight:800;
      }

      #ray-version {
        position:absolute;
        right:13px;
        top:8px;
        font-size:12px;
        opacity:.75;
      }

      #ray-updated {
        position:absolute;
        right:13px;
        bottom:8px;
        font-size:12px;
        opacity:.75;
      }

      /* ================= SIDEBAR ================= */

      #ray-sidebar {
        position:fixed;

        z-index:2147483645;

        top:var(--ray-header);
        bottom:0;
        left:0;

        width:var(--ray-side);

        overflow:auto;

        background:#f1f5f9;

        border-right:1px solid #c9d3de;

        font-family:
          "Noto Sans JP",
          "Yu Gothic",
          Meiryo,
          sans-serif;
      }

      .ray-section-title {
        padding:9px 14px;

        background:#0b2d57;

        color:#fff;

        font-size:19px;
        font-weight:900;
      }

      .ray-list {
        padding:6px 8px 3px;
      }

      .ray-card {
        padding:8px 9px;

        margin-bottom:5px;

        background:#fff;

        border:1px solid #d4dde7;

        border-radius:7px;
      }

      .ray-card-top {
        display:flex;
        align-items:center;
        gap:6px;
      }

      .ray-cat {
        flex:none;

        padding:3px 5px;

        border-radius:3px;

        background:#405b78;

        color:#fff;

        font-size:11px;
        font-weight:900;
      }

      .ray-title {
        font-size:15px;
        font-weight:900;
        color:#17212d;
      }

      .ray-card-bottom {
        display:flex;
        justify-content:space-between;
        margin-top:3px;
      }

      .ray-date {
        font-size:15px;
        font-weight:800;
      }

      .ray-days {
        font-size:17px;
        font-weight:900;
        color:#1769aa;
      }

      .ray-days.orange {
        color:#e37800;
      }

      .ray-days.red {
        color:#d92727;
      }

      #ray-settings {
        display:block;

        margin:6px 8px 15px;
        padding:7px;

        text-align:center;
        text-decoration:none;

        border:1px solid #cad3dc;
        border-radius:5px;

        background:#e4eaf1;
        color:#34495e;

        font-size:12px;
        font-weight:800;
      }

      /* ================= MAIN ================= */

      #ray-monitor {
        position:fixed;

        z-index:2147483644;

        left:var(--ray-side);
        right:0;
        top:var(--ray-header);
        bottom:0;

        background:#eaf0f5;

        padding:7px;

        box-sizing:border-box;

        overflow:hidden;

        font-family:
          "Noto Sans JP",
          "Yu Gothic",
          Meiryo,
          sans-serif;
      }

      #ray-monitor.hidden {
        display:none;
      }

      /* ================= TOOLBAR ================= */

      #ray-toolbar {
        height:58px;

        box-sizing:border-box;

        background:#fff;

        border:1px solid #d2dbe5;
        border-radius:7px;

        padding:6px 10px;
        margin-bottom:6px;

        display:flex;
        align-items:center;
        justify-content:space-between;
      }

      #ray-toolbar-left {
        display:flex;
        align-items:center;
        gap:8px;
      }

      #ray-monitor-title {
        font-size:21px;
        font-weight:900;
        color:#0b2d57;
        margin-right:8px;
      }

      #ray-time-select {
        height:34px;

        border:1px solid #b9c5d2;
        border-radius:5px;

        padding:0 8px;

        font-size:14px;
        font-weight:900;
      }

      .ray-btn {
        height:34px;

        padding:0 11px;

        border-radius:5px;
        border:1px solid #c4ced9;

        background:#eef2f6;
        color:#20354b;

        font-size:13px;
        font-weight:900;

        cursor:pointer;
      }

      .ray-btn.blue {
        background:#0b2d57;
        color:#fff;
        border-color:#0b2d57;
      }

      #ray-scan-status {
        font-size:12px;
        color:#677482;
        font-weight:800;
      }

      /* ================= 2 TIME COLUMNS ================= */

      #ray-two-columns {
        height:calc(100% - 64px);

        display:grid;

        grid-template-columns:
          minmax(0,1fr)
          minmax(0,1fr);

        gap:7px;
      }

      .ray-time-column {
        min-width:0;
        height:100%;

        background:#fff;

        border:1px solid #ccd6e1;
        border-radius:7px;

        overflow:hidden;

        display:flex;
        flex-direction:column;
      }

      .ray-time-head {
        flex:none;

        height:44px;

        display:flex;
        justify-content:center;
        align-items:center;

        background:#0b2d57;
        color:#fff;

        font-size:23px;
        font-weight:900;
      }

      .ray-current {
        margin-left:7px;
        padding:2px 6px;

        border-radius:3px;

        background:#fff;
        color:#d92727;

        font-size:10px;
      }

      /* ================= ROOMS ================= */

      .ray-rooms {
        flex:1;
        min-height:0;

        padding:5px;

        display:grid;

        grid-template-columns:
          minmax(0,1fr)
          minmax(0,1fr);

        grid-template-rows:
          minmax(0, var(--ray-upper-fr, 50fr))
          8px
          minmax(0, var(--ray-lower-fr, 50fr));

        gap:5px;

        overflow:hidden;

        background:#f2f6f9;
      }

      /* v8.7: ①② / ③④ の高さをドラッグで調整 */
      .ray-room.room-1,
      .ray-room.room-2 {
        grid-row:1;
      }

      .ray-room.room-3,
      .ray-room.room-4 {
        grid-row:3;
      }

      .ray-room-divider {
        grid-column:1 / -1;
        grid-row:2;

        min-height:8px;
        border-radius:4px;

        cursor:ns-resize;
        touch-action:none;

        background:
          linear-gradient(
            to bottom,
            transparent 2px,
            #9fb2c4 2px,
            #9fb2c4 6px,
            transparent 6px
          );

        position:relative;
        z-index:5;
      }

      .ray-room-divider:hover,
      .ray-room-divider.ray-dragging {
        background:
          linear-gradient(
            to bottom,
            transparent 1px,
            #0b2d57 1px,
            #0b2d57 7px,
            transparent 7px
          );
      }

      .ray-room {
        min-width:0;
        min-height:0;

        border:1px solid #cbd6e1;
        border-radius:5px;

        background:#fff;

        overflow:hidden;

        display:flex;
        flex-direction:column;
      }

      .ray-room-head {
        flex:none;

        padding:6px 8px;

        background:#dbe8f3;
        color:#0b2d57;

        font-size:17px;
        line-height:1;
        font-weight:900;

        border-bottom:1px solid #cad7e2;
      }

      .ray-room-body {
        flex:1;
        min-height:0;

        padding:3px;

        /* v8.7: 通常は仕切りで調整。入り切らない場合だけ教室内スクロール */
        overflow-x:hidden;
        overflow-y:auto;
        scrollbar-width:thin;

        display:grid;

        grid-template-columns:1fr;

        align-content:start;

        gap:3px;
      }

      /*
        ②番教室
        最大4ブース
        1 2
        3 4
      */
      .room-2 .ray-room-body {
        grid-template-columns:
          minmax(0,1fr)
          minmax(0,1fr);

        grid-auto-flow:row;
        grid-auto-rows:max-content;

        align-content:start;
      }

      /*
        ③番教室
        最大8ブース
        1 2
        3 4
        5 6
        7 8
      */
      .room-3 .ray-room-body {
        grid-template-columns:
          minmax(0,1fr)
          minmax(0,1fr);

        grid-auto-flow:row;
        grid-auto-rows:max-content;

        align-content:start;
      }

      .room-4 .ray-room-body {
        grid-template-columns:1fr;
      }

      /* ================= BOOTH ================= */

      .ray-booth {
        min-width:0;

        border:1px solid #d8e0e8;
        border-radius:4px;

        overflow:hidden;

        background:#fff;
      }

      .ray-booth-head {
        min-height:27px;

        box-sizing:border-box;

        padding:4px 7px;

        display:flex;
        align-items:center;
        justify-content:space-between;

        background:#edf3f8;
        color:#20384f;

        font-size:13px;
        line-height:1.1;
        font-weight:900;
      }

      .ray-count {
        flex:none;

        margin-left:4px;

        color:#657381;

        font-size:11px;
      }

      /* ================= TEACHER ================= */

      /* v6.1: 専用モニターからComiru標準編集を呼び出す */
      .ray-teacher,
      .ray-student {
        cursor:pointer;
      }

      .ray-teacher:hover,
      .ray-student:hover {
        outline:2px solid rgba(11,45,87,.28);
        outline-offset:-2px;
      }

      .ray-teacher {
        min-height:27px;

        box-sizing:border-box;

        padding:5px 7px;

        border-left:5px solid #0b2d57;

        background:#dce8f2;
        color:#142b42;

        font-size:14px;
        line-height:1.15;
        font-weight:900;

        white-space:nowrap;
        overflow:hidden;
        text-overflow:ellipsis;
      }

      /* ================= STUDENT ================= */

      .ray-student {
        position:relative;

        min-height:29px;

        box-sizing:border-box;

        padding:5px 7px 5px 11px;

        display:flex;
        align-items:center;

        gap:6px;

        border-bottom:1px solid #e1e6eb;
      }

      .ray-student:last-child {
        border-bottom:0;
      }

      .ray-student-name {
        flex:1;
        min-width:0;

        font-size:14px;
        line-height:1.2;
        font-weight:900;

        color:#17212d;

        white-space:nowrap;
        overflow:hidden;
        text-overflow:ellipsis;
      }

      /* ================= SUBJECT ================= */

      .ray-subject {
        flex:none;

        max-width:120px;

        padding:3px 6px;

        border-radius:4px;

        background:#dff4f1;
        color:#087d78;

        font-size:10.5px;
        line-height:1.1;
        font-weight:900;

        white-space:nowrap;
        overflow:hidden;
        text-overflow:ellipsis;
      }

      .ray-extra {
        flex:none;
        max-width:140px;
        padding:3px 6px;
        border-radius:4px;
        font-size:10.5px;
        line-height:1.1;
        font-weight:900;
        white-space:nowrap;
        overflow:hidden;
        text-overflow:ellipsis;
      }

      .ray-extra.ray-absence {
        background:#e53935;
        color:#fff;
      }

      .ray-extra.ray-reflection {
        background:#fff0b3;
        color:#7a5200;
      }

      /* v7.1 新規・初回 */
      .ray-entry-badge {
        flex:none;
        padding:3px 7px;
        border-radius:999px;
        font-size:10.5px;
        line-height:1.1;
        font-weight:900;
        white-space:nowrap;
      }

      .ray-entry-badge.ray-first {
        background:#7b1fa2;
        color:#fff;
      }

      .ray-entry-badge.ray-new {
        background:#1565c0;
        color:#fff;
      }

      /* =================================================
         v7.2 生徒ホバーカード
         ================================================= */

      .ray-student {
        cursor:pointer;
      }

      #ray-student-card {
        position:fixed;
        z-index:2147483647;
        width:340px;
        max-width:calc(100vw - 24px);
        background:#fff;
        border:2px solid #0b3766;
        border-radius:10px;
        box-shadow:0 10px 30px rgba(0,0,0,.28);
        padding:12px 14px;
        color:#172536;
        font-size:13px;
        line-height:1.45;
        display:none;
        pointer-events:auto;
      }

      #ray-student-card.ray-show {
        display:block;
      }

      .ray-card-head {
        display:flex;
        align-items:center;
        gap:7px;
        padding-bottom:8px;
        margin-bottom:8px;
        border-bottom:1px solid #d7e1ec;
      }

      .ray-card-name {
        font-size:17px;
        font-weight:900;
        color:#0b3766;
      }

      .ray-card-badge {
        padding:2px 7px;
        border-radius:999px;
        font-size:11px;
        font-weight:900;
        color:#fff;
      }

      .ray-card-badge.ray-first {
        background:#7b1fa2;
      }

      .ray-card-badge.ray-new {
        background:#1565c0;
      }

      .ray-card-row {
        display:grid;
        grid-template-columns:78px 1fr;
        gap:6px;
        margin:5px 0;
      }

      .ray-card-label {
        font-weight:900;
        color:#52667c;
      }

      .ray-card-value {
        font-weight:700;
        overflow-wrap:anywhere;
      }

      .ray-card-alert {
        color:#c62828;
        font-weight:900;
      }

      .ray-card-note {
        margin-top:8px;
        padding:7px 9px;
        border-radius:7px;
        background:#f3f6f9;
        white-space:normal;
        overflow-wrap:anywhere;
      }

      .ray-card-hint {
        margin-top:8px;
        font-size:11px;
        color:#74869a;
      }

      .ray-card-section {
        margin-top:9px;
        padding-top:8px;
        border-top:1px solid #d7e1ec;
      }

      .ray-card-section-title {
        margin-bottom:5px;
        font-weight:900;
        color:#0b3766;
      }

      .ray-card-loading {
        color:#607d8b;
        font-weight:700;
      }

      .ray-card-score {
        font-weight:800;
        line-height:1.65;
      }

      .ray-card-source {
        margin-top:6px;
        font-size:10.5px;
        color:#7a8998;
      }


      /* v8.2 ReaLTE要点表示 */
      .ray-card-summary {
        margin-top:7px;
        padding:8px 9px;
        border-radius:7px;
        background:#f5f8fb;
      }

      .ray-card-summary-block + .ray-card-summary-block {
        margin-top:7px;
      }

      .ray-card-summary-title {
        font-weight:900;
        color:#0b3766;
        margin-bottom:2px;
      }

      .ray-card-summary-line {
        font-size:12px;
        line-height:1.45;
        font-weight:700;
      }

      .ray-card-details {
        margin-top:7px;
      }

      .ray-card-details summary {
        cursor:pointer;
        color:#52667c;
        font-size:11px;
        font-weight:900;
        pointer-events:auto;
      }

      .ray-card-details .ray-card-note {
        font-size:11.5px;
        max-height:150px;
        overflow:auto;
      }

      /* ================= SCHOOL LEVEL ================= */

      .ray-student.ray-elementary {
        border-left:6px solid #32a852;

        background:
          linear-gradient(
            90deg,
            rgba(50,168,82,.12),
            rgba(50,168,82,.035) 40%,
            #fff 100%
          );
      }

      .ray-student.ray-junior {
        border-left:6px solid #1976d2;

        background:
          linear-gradient(
            90deg,
            rgba(25,118,210,.12),
            rgba(25,118,210,.035) 40%,
            #fff 100%
          );
      }

      .ray-student.ray-high {
        border-left:6px solid #ef8b18;

        background:
          linear-gradient(
            90deg,
            rgba(239,139,24,.13),
            rgba(239,139,24,.035) 40%,
            #fff 100%
          );
      }

      .ray-student.ray-other {
        border-left:6px solid #9aa5af;
      }

      .ray-empty-seat {
        padding:5px;

        color:#9ba5af;

        text-align:center;

        font-size:11px;
      }

      .ray-no-data {
        padding:30px;

        text-align:center;

        color:#65717d;

        font-size:16px;
        font-weight:800;
      }
    `;

    document.head.appendChild(style);
  }


  // =====================================================
  // HEADER
  // =====================================================

  function createHeader() {
    const h = document.createElement('div');

    h.id = 'ray-header';

    h.innerHTML = `
      <div id="ray-logo">
        <img src="${LOGO_URL}">
      </div>

      <div id="ray-head-main">

        <div id="ray-version">
          v${VERSION}
        </div>

        <div id="ray-slogan-label">
          今週の目標
        </div>

        <div id="ray-slogan">
          目標を読み込み中...
        </div>


        <div id="ray-updated"></div>

      </div>
    `;

    document.body.appendChild(h);
  }


  // =====================================================
  // SIDEBAR
  // =====================================================

  function createSidebar() {
    const s = document.createElement('div');

    s.id = 'ray-sidebar';

    s.innerHTML = `
      <div class="ray-section-title">
        入試 COUNTDOWN
      </div>

      <div
        id="ray-exams"
        class="ray-list">
      </div>

      <div class="ray-section-title">
        直近のイベント
      </div>

      <div
        id="ray-events"
        class="ray-list">
      </div>

      <a
        id="ray-settings"
        href="${SETTINGS_URL}"
        target="_blank">
        モニター設定を開く
      </a>
    `;

    document.body.appendChild(s);
  }

  function parseDate(v) {
    const m = String(v || '').match(
      /^(\d{4})-(\d{1,2})-(\d{1,2})/
    );

    if (!m) return null;

    return new Date(
      Number(m[1]),
      Number(m[2]) - 1,
      Number(m[3])
    );
  }

  function daysUntil(v) {
    const target = parseDate(v);

    if (!target) return null;

    const n = new Date();

    const today = new Date(
      n.getFullYear(),
      n.getMonth(),
      n.getDate()
    );

    return Math.round(
      (target - today) /
      86400000
    );
  }

  function dateText(item) {
    if (item.dateText) {
      return item.dateText;
    }

    const d = parseDate(item.date);

    if (!d) return '';

    return (
      `${d.getMonth() + 1}/` +
      `${d.getDate()}`
    );
  }

  function renderList(
    id,
    source,
    max
  ) {
    const el =
      document.getElementById(id);

    if (!el) return;

    const items =
      (source || [])
        .filter(x => {
          const d =
            daysUntil(x.date);

          return (
            d !== null &&
            d >= 0
          );
        })
        .sort(
          (a, b) =>
            parseDate(a.date) -
            parseDate(b.date)
        )
        .slice(0, max);

    el.innerHTML = '';

    items.forEach(item => {
      const days =
        daysUntil(item.date);

      let cls = '';

      if (days <= 7) {
        cls = 'red';

      } else if (days <= 30) {
        cls = 'orange';
      }

      const card =
        document.createElement(
          'div'
        );

      card.className =
        'ray-card';

      card.innerHTML = `
        <div class="ray-card-top">

          <span class="ray-cat">
            ${esc(
              item.category ||
              item.type ||
              '予定'
            )}
          </span>

          <span class="ray-title">
            ${esc(
              item.title ||
              item.name ||
              item.school ||
              '予定'
            )}
          </span>

        </div>

        <div class="ray-card-bottom">

          <span class="ray-date">
            ${esc(dateText(item))}
          </span>

          <span class="ray-days ${cls}">
            ${
              days === 0
                ? '今日！'
                : `あと${days}日`
            }
          </span>

        </div>
      `;

      el.appendChild(card);
    });
  }


  // =====================================================
  // API
  // =====================================================

  function getSloganFromApi(data) {
    /*
      APIで現在確認できている形：

      {
        "settings": {
          "slogan": "..."
        },
        ...
      }

      旧形式の
      data.slogan
      にも対応させる。
    */

    const candidates = [
      data?.settings?.slogan,
      data?.slogan,
      data?.settings?.weeklySlogan,
      data?.weeklySlogan
    ];

    for (const value of candidates) {
      const text = clean(value);

      if (text) {
        return text;
      }
    }

    return '';
  }

  function fetchSidebar() {
    GM_xmlhttpRequest({
      method: 'GET',

      url:
        API_URL +
        '&t=' +
        Date.now(),

      headers: {
        'Cache-Control': 'no-cache',
        'Pragma': 'no-cache'
      },

      timeout: 15000,

      onload(res) {
        try {
          const text =
            String(
              res.responseText ||
              ''
            ).trim();

          const data =
            JSON.parse(text);

          console.log(
            '[RAYS API DATA]',
            data
          );

          /*
            v7.1
            今日の初回授業・新規入塾を保持
          */
          firstLessonItems =
            Array.isArray(
              data.firstLessons
            )
              ? data.firstLessons
              : [];

          newStudentItems =
            Array.isArray(
              data.newStudents
            )
              ? data.newStudents
              : [];

          /*
            API取得後すぐに座席表示へ反映
          */
          if (customMode) {
            render();
          }

          /*
            v6.0
            settings.slogan を最優先
          */
          const slogan =
            getSloganFromApi(data);

          const sloganEl =
            document.getElementById(
              'ray-slogan'
            );

          if (sloganEl) {
            sloganEl.textContent =
              slogan ||
              '目標未設定';
          }

          /*
            お知らせ

            settings.notices
            data.notices
            どちらにも対応
          */
          // v6.0: ヘッダーは「今週の目標」だけ表示する。
          // 連絡事項はComiruモニター上部には表示しない。
          const noticeSource = [];

          const notices =
            document.getElementById(
              'ray-notices'
            );

          if (notices) {
            notices.innerHTML = '';

            (
              Array.isArray(noticeSource)
                ? noticeSource
                : []
            )
              .forEach(n => {
                const text =
                  typeof n === 'string'
                    ? n
                    : (
                        n.content ||
                        n.text ||
                        n.title ||
                        ''
                      );

                if (!text) return;

                const div =
                  document.createElement(
                    'div'
                  );

                div.className =
                  'ray-notice';

                div.textContent =
                  text;

                notices.appendChild(
                  div
                );
              });
          }

          renderList(
            'ray-exams',
            data.entrance || [],
            MAX_ENTRANCE
          );

          renderList(
            'ray-events',
            data.events || [],
            MAX_EVENTS
          );

          updateClock();

        } catch (e) {
          console.error(
            '[RAYS API PARSE ERROR]',
            e,
            res.responseText
          );

          const sloganEl =
            document.getElementById(
              'ray-slogan'
            );

          if (
            sloganEl &&
            (
              sloganEl.textContent ===
              '目標を読み込み中...'
            )
          ) {
            sloganEl.textContent =
              '目標取得エラー';
          }
        }
      },

      onerror(err) {
        console.error(
          '[RAYS API NETWORK ERROR]',
          err
        );

        const sloganEl =
          document.getElementById(
            'ray-slogan'
          );

        if (
          sloganEl &&
          sloganEl.textContent ===
          '目標を読み込み中...'
        ) {
          sloganEl.textContent =
            '目標取得エラー';
        }
      },

      ontimeout() {
        console.error(
          '[RAYS API TIMEOUT]'
        );
      }
    });
  }

  function updateClock() {
    const el =
      document.getElementById(
        'ray-updated'
      );

    if (!el) return;

    const n = new Date();

    el.textContent =
      `更新 ` +
      `${String(n.getHours()).padStart(2, '0')}:` +
      `${String(n.getMinutes()).padStart(2, '0')} / ` +
      `v${VERSION}`;
  }


  // =====================================================
  // MAIN
  // =====================================================

  function createMain() {
    const m =
      document.createElement(
        'div'
      );

    m.id = 'ray-monitor';

    m.innerHTML = `
      <div id="ray-toolbar">

        <div id="ray-toolbar-left">

          <div id="ray-monitor-title">
            ${IS_EKINAN_SCHOOL ? '駅南校' : '本校'}　本日の座席状況
          </div>

          <select
            id="ray-time-select">
          </select>

          <button
            id="ray-now"
            class="ray-btn blue">
            現在
          </button>

          <button
            id="ray-next"
            class="ray-btn">
            次の2コマ ▶
          </button>

          <span id="ray-scan-status">
            座席情報取得中...
          </span>

        </div>

        <div>

          <button
            id="ray-refresh"
            class="ray-btn blue">
            全座席を再取得
          </button>

          <button
            id="ray-layout-edit"
            class="ray-btn blue">
            生徒・講師を配置
          </button>

          <button
            id="ray-comiru"
            class="ray-btn">
            Comiru標準画面
          </button>

        </div>

      </div>

      <div id="ray-two-columns">

        <div class="ray-no-data">
          Comiru座席表を解析しています...
        </div>

      </div>
    `;

    document.body.appendChild(m);

    document
      .getElementById(
        'ray-time-select'
      )
      .addEventListener(
        'change',
        e => {
          setManualTime(
            e.target.value
          );

          render();
        }
      );

    document
      .getElementById(
        'ray-now'
      )
      .addEventListener(
        'click',
        () => {
          returnToAutoTime();
          render();
        }
      );

    document
      .getElementById(
        'ray-next'
      )
      .addEventListener(
        'click',
        () => {
          const times =
            getAllTimes();

          const shown =
            chooseTimes(times);

          if (!shown.length) {
            return;
          }

          const last =
            shown[
              shown.length - 1
            ];

          const next =
            times.find(
              t =>
                t.start >
                last.start
            );

          if (next) {
            setManualTime(
              next.start
            );

            render();
          }
        }
      );

    document
      .getElementById(
        'ray-refresh'
      )
      .addEventListener(
        'click',
        async () => {
          await scanWholeComiru();
        }
      );

    document
      .getElementById(
        'ray-layout-edit'
      )
      .addEventListener(
        'click',
        openComiruPlacementEditor
      );

    document
      .getElementById(
        'ray-comiru'
      )
      .addEventListener(
        'click',
        showComiru
      );
  }


  // =====================================================
  // COMIRU TABLE
  // =====================================================

  function getSeatTables() {
    return [
      ...document.querySelectorAll(
        'table.day-seat-detail'
      )
    ];
  }

  function findScrollableParents() {
    const found =
      new Set();

    getSeatTables()
      .forEach(table => {
        let p =
          table.parentElement;

        while (
          p &&
          p !== document.body
        ) {
          const cs =
            getComputedStyle(p);

          const canY =
            /(auto|scroll)/
              .test(
                cs.overflowY
              ) &&
            p.scrollHeight >
              p.clientHeight + 5;

          const canX =
            /(auto|scroll)/
              .test(
                cs.overflowX
              ) &&
            p.scrollWidth >
              p.clientWidth + 5;

          if (canY || canX) {
            found.add(p);
          }

          p = p.parentElement;
        }
      });

    return [...found];
  }


  // =====================================================
  // TIME
  // =====================================================

  function getCellIndex(table) {
    let el =
      table.parentElement;

    while (el) {
      if (
        el.tagName === 'TD'
      ) {
        return el.cellIndex;
      }

      el =
        el.parentElement;
    }

    return null;
  }

  function findColumnTime(
    cellIndex
  ) {
    if (
      cellIndex === null
    ) {
      return null;
    }

    const rows = [
      ...document.querySelectorAll(
        'tr'
      )
    ];

    for (const row of rows) {
      const cell =
        row.cells?.[
          cellIndex
        ];

      if (!cell) {
        continue;
      }

      const t =
        extractTime(
          cell.innerText
        );

      if (t) {
        return t;
      }
    }

    return null;
  }


  // =====================================================
  // STUDENTS
  // =====================================================

  function getRealStudentNodes(
    table
  ) {
    const direct = [
      ...table.querySelectorAll(
        '.seat-student-info'
      )
    ];

    return [
      ...new Set(direct)
    ];
  }

  function getStudentName(node) {
    const direct = [
      ...node.children
    ].filter(
      el =>
        el.matches?.(
          'span.text-black'
        )
    );

    for (const span of direct) {
      const v =
        clean(
          span.textContent
        );

      if (
        validStudentName(v)
      ) {
        return v;
      }
    }

    const spans = [
      ...node.querySelectorAll(
        'span.text-black'
      )
    ];

    for (const span of spans) {
      if (
        span.closest(
          '.subject-tag'
        ) ||
        span.closest(
          '.seat-student-detail-container'
        ) ||
        span.closest(
          '.vue-component-tooltip'
        ) ||
        span.closest(
          'button'
        )
      ) {
        continue;
      }

      const v =
        clean(
          span.textContent
        );

      if (
        validStudentName(v)
      ) {
        return v;
      }
    }

    return '';
  }

  function validStudentName(v) {
    v = clean(v);

    if (!v) {
      return false;
    }

    if (
      /^\d+\s*\/\s*\d+$/
        .test(v)
    ) {
      return false;
    }

    if (
      /[（(]\s*レ\s*[\/／]\s*振\s*[）)]/
        .test(v)
    ) {
      return false;
    }

    if (
      /^レ\s*[\/／]\s*振$/
        .test(v)
    ) {
      return false;
    }

    if (
      /^\d{1,2}:\d{2}/
        .test(v)
    ) {
      return false;
    }

    if (
      /^(再配当|欠席|振替|講師|生徒|登録なし|未設定|公開|編集|削除|更新|キャンセル|枠)$/
        .test(v)
    ) {
      return false;
    }

    if (
      /教室|ブース/
        .test(v)
    ) {
      return false;
    }

    if (
      v.length > 60
    ) {
      return false;
    }

    return true;
  }

  function getStudentSubject(
    node
  ) {
    /*
      科目名の固定リストは使用しない。

      Comiruのsubject-tagを
      そのまま取得するため、
      科目が増えても対応できる。
    */

    return clean(
      node
        .querySelector(
          '.subject-tag'
        )
        ?.textContent
    );
  }

  function getStudentExtraInfo(node) {
    /*
      v6.6
      Comiru純正の生徒カード内に表示される
      ・欠席（振替不可／振替済み等）
      ・学生のノート「テスト振り返り」
      を取得する。

      class名だけに依存せず、生徒カード内の表示文字も見ることで
      Comiru側の軽微なHTML変更に耐えやすくする。
    */
    const text = clean(node.innerText || node.textContent || '');

    let absence = '';
    const absenceMatch = text.match(
      /欠席\s*[（(]\s*振替\s*(?:不可|済み|済|可)\s*[）)]/
    );

    if (absenceMatch) {
      absence = clean(absenceMatch[0])
        .replace(/\(\s*/g, '（')
        .replace(/\s*\)/g, '）');
    } else if (/欠席/.test(text)) {
      const shortMatch = text.match(/欠席(?:\s*（[^）]{1,12}）)?/);
      absence = shortMatch ? clean(shortMatch[0]) : '欠席';
    }

    let reflection = '';
    if (/テスト\s*振り返り/.test(text)) {
      reflection = 'テスト振り返り';
    }

    return {
      absence,
      reflection
    };
  }

  function parseStudents(
    table
  ) {
    const nodes =
      getRealStudentNodes(
        table
      );

    const result = [];
    const seen =
      new Set();

    nodes.forEach(
      (node, index) => {

        const name =
          getStudentName(node);

        if (!name) {
          return;
        }

        const subject =
          getStudentSubject(
            node
          );

        const extra =
          getStudentExtraInfo(
            node
          );

        const seatStudentId =
          clean(
            node.getAttribute(
              'data-seat-student-id'
            ) ||
            node.dataset
              ?.seatStudentId ||
            ''
          );

        const studentId =
          clean(
            node.getAttribute(
              'data-student-id'
            ) ||
            node.dataset
              ?.studentId ||
            ''
          );

        const key =
          seatStudentId ||
          (
            studentId
              ? (
                  studentId +
                  '|' +
                  subject
                )
              : (
                  name +
                  '|' +
                  subject +
                  '|' +
                  index
                )
          );

        if (
          seen.has(key)
        ) {
          return;
        }

        seen.add(key);

        result.push({
          id:key,
          seatStudentId,
          studentId,
          name,
          subject,
          absence: extra.absence || '',
          reflection: extra.reflection || ''
        });
      }
    );

    return result;
  }


  // =====================================================
  // BOOTH
  // =====================================================

  function parseBooth(table) {
    let booth = '';

    const candidates = [
      ...table.querySelectorAll(
        '.seat-detail-info .text-black'
      )
    ];

    for (
      const c of candidates
    ) {
      const v =
        clean(
          c.textContent
        );

      if (
        /教室|ブース|駅南/
          .test(v)
      ) {
        booth = v;
        break;
      }
    }

    if (!booth) {
      booth =
        clean(
          table
            .querySelector(
              '.seat-detail-info .seat-detail-item'
            )
            ?.textContent
        );
    }

    const teacher =
      clean(
        table
          .querySelector(
            '.seat-teacher-area--name'
          )
          ?.textContent
      );

    const count =
      clean(
        table
          .querySelector(
            '.seat-student-area .mt-8 .text-black'
          )
          ?.textContent
      );

    return {
      booth:
        booth ||
        'ブース',

      teacher,

      count,

      students:
        parseStudents(table)
    };
  }


  // =====================================================
  // MERGE STUDENTS
  // =====================================================

  function mergeStudents(
    oldStudents,
    newStudents
  ) {
    const map =
      new Map();

    [
      ...(oldStudents || []),
      ...(newStudents || [])
    ].forEach(student => {

      const key =
        student.seatStudentId ||
        (
          student.studentId
            ? (
                student.studentId +
                '|' +
                student.subject
              )
            : (
                student.name +
                '|' +
                student.subject
              )
        );

      if (!key) {
        return;
      }

      map.set(
        key,
        student
      );
    });

    return [
      ...map.values()
    ];
  }


  // =====================================================
  // CAPTURE
  // =====================================================

  function captureVisibleSeats() {
    const tables =
      getSeatTables();

    tables.forEach(table => {
      const cellIndex =
        getCellIndex(table);

      const time =
        findColumnTime(
          cellIndex
        );

      if (!time) {
        return;
      }

      const seat =
        parseBooth(table);

      const seatId =
        table.dataset.seatId ||
        seat.booth;

      const key =
        `${time.label}|${seatId}`;

      const old =
        seatCache.get(key);

      if (old) {
        seat.students =
          mergeStudents(
            old.students,
            seat.students
          );

        if (!seat.teacher) {
          seat.teacher =
            old.teacher;
        }

        if (!seat.count) {
          seat.count =
            old.count;
        }

        if (!seat.booth) {
          seat.booth =
            old.booth;
        }
      }

      seatCache.set(
        key,
        {
          ...seat,

          time:
            time.label,

          start:
            time.start,

          end:
            time.end,

          seatId
        }
      );
    });
  }


  // =====================================================
  // SCROLL SCAN
  // =====================================================

  async function scanElement(
    el
  ) {
    const originalTop =
      el.scrollTop;

    const originalLeft =
      el.scrollLeft;

    const maxY =
      Math.max(
        0,
        el.scrollHeight -
        el.clientHeight
      );

    const maxX =
      Math.max(
        0,
        el.scrollWidth -
        el.clientWidth
      );

    const stepY =
      Math.max(
        100,
        Math.floor(
          el.clientHeight *
          .45
        )
      );

    const stepX =
      Math.max(
        100,
        Math.floor(
          el.clientWidth *
          .45
        )
      );

    const xs = [0];

    for (
      let x = stepX;
      x < maxX;
      x += stepX
    ) {
      xs.push(x);
    }

    if (
      maxX > 0 &&
      xs[
        xs.length - 1
      ] !== maxX
    ) {
      xs.push(maxX);
    }

    const ys = [0];

    for (
      let y = stepY;
      y < maxY;
      y += stepY
    ) {
      ys.push(y);
    }

    if (
      maxY > 0 &&
      ys[
        ys.length - 1
      ] !== maxY
    ) {
      ys.push(maxY);
    }

    for (
      const y of ys
    ) {
      for (
        const x of xs
      ) {
        el.scrollTop = y;
        el.scrollLeft = x;

        await sleep(220);

        captureVisibleSeats();

        await sleep(120);

        captureVisibleSeats();
      }
    }

    el.scrollTop =
      originalTop;

    el.scrollLeft =
      originalLeft;

    await sleep(180);

    captureVisibleSeats();
  }


  // =====================================================
  // SEND SNAPSHOT TO UNIFIED DASHBOARD
  // =====================================================

  function sendSeatSnapshot() {
    const seats =
      [
        ...seatCache.values()
      ].map(
        seat => ({
          time:
            seat.time || '',

          classroom:
            '',

          booth:
            seat.booth || '',

          teacher:
            seat.teacher || '',

          seatId:
            seat.seatId || '',

          students:
            (seat.students || []).map(
              student => ({
                name:
                  student.name || '',

                grade:
                  student.grade || '',

                subject:
                  student.subject || '',

                studentId:
                  student.studentId || '',

                seatStudentId:
                  student.seatStudentId || '',

                absence:
                  student.absence || '',

                reflection:
                  student.reflection || ''
              })
            )
        })
      );

    if (!seats.length) {
      return;
    }

    GM_xmlhttpRequest({
      method:
        'POST',

      url:
        API_BASE_URL,

      headers: {
        'Content-Type':
          'application/json'
      },

      data:
        JSON.stringify({
          type:
            'comiruSeatSnapshot',

          version:
            VERSION,

          capturedAt:
            new Date()
              .toISOString(),

          seats:
            seats
        }),

      onload(res) {
        try {
          const data =
            JSON.parse(
              res.responseText ||
              '{}'
            );

          if (!data.ok) {
            console.error(
              '[RAYS] 座席ログ保存エラー',
              data
            );
          }

        } catch(e) {
          console.error(
            '[RAYS] 座席ログ応答解析エラー',
            e
          );
        }
      },

      onerror(err) {
        console.error(
          '[RAYS] 座席ログ送信エラー',
          err
        );
      }
    });
  }


  // =====================================================
  // FULL SCAN
  // =====================================================

  async function scanWholeComiru() {
    if (scanning) {
      return;
    }

    scanning = true;

    const status =
      document.getElementById(
        'ray-scan-status'
      );

    if (status) {
      status.textContent =
        '全座席を取得中…';
    }

    /*
      古い座席データを消して
      現在のComiruから再取得
    */
    seatCache.clear();

    captureVisibleSeats();

    const scrollers =
      findScrollableParents();

    for (
      let i = 0;
      i < scrollers.length;
      i++
    ) {
      if (status) {
        status.textContent =
          `全座席を取得中… ` +
          `${i + 1}/` +
          `${scrollers.length}`;
      }

      await scanElement(
        scrollers[i]
      );
    }

    const oldX =
      window.scrollX;

    const oldY =
      window.scrollY;

    const maxWindowY =
      Math.max(
        0,
        document
          .documentElement
          .scrollHeight -
        window.innerHeight
      );

    const step =
      Math.max(
        220,
        Math.floor(
          window.innerHeight *
          .50
        )
      );

    const positions = [0];

    for (
      let y = step;
      y < maxWindowY;
      y += step
    ) {
      positions.push(y);
    }

    if (
      maxWindowY > 0 &&
      positions[
        positions.length - 1
      ] !== maxWindowY
    ) {
      positions.push(
        maxWindowY
      );
    }

    for (
      const y of positions
    ) {
      window.scrollTo(
        oldX,
        y
      );

      await sleep(220);

      captureVisibleSeats();

      await sleep(120);

      captureVisibleSeats();
    }

    window.scrollTo(
      oldX,
      oldY
    );

    await sleep(200);

    captureVisibleSeats();

    scanning = false;

    updateScanStatus();

    // v6.0
    // 統合SSへ現在の全座席スナップショットを送信
    sendSeatSnapshot();

    render();
  }


  // =====================================================
  // STATUS
  // =====================================================

  function updateScanStatus() {
    const status =
      document.getElementById(
        'ray-scan-status'
      );

    if (!status) {
      return;
    }

    const studentCount =
      [
        ...seatCache.values()
      ].reduce(
        (sum, seat) =>
          sum +
          (
            seat.students
              ?.length ||
            0
          ),
        0
      );

    const mode =
      manualStart === null
        ? '自動'
        : '手動';

    status.textContent =
      `${seatCache.size}座席 / ` +
      `生徒配置${studentCount}件 / ` +
      `${mode}`;
  }


  // =====================================================
  // CLASSROOM
  // =====================================================

  function classroomNumber(name) {
    const v =
      String(name || '');

    if (
      /①|1番教室/
        .test(v)
    ) {
      return 1;
    }

    if (
      /②|2番教室/
        .test(v)
    ) {
      return 2;
    }

    if (
      /③|3番教室/
        .test(v)
    ) {
      return 3;
    }

    if (
      /④|4番教室/
        .test(v)
    ) {
      return 4;
    }

    return 4;
  }

  function boothNumber(name) {
    const m =
      String(name || '')
        .match(
          /ブース\s*(\d+)/
        );

    return m
      ? Number(m[1])
      : 999;
  }


  // =====================================================
  // TIMES
  // =====================================================

  function getAllTimes() {
    const map =
      new Map();

    seatCache.forEach(
      seat => {

        if (!seat.time) {
          return;
        }

        if (
          EXCLUDED_TIMES
            .has(
              seat.time
            )
        ) {
          return;
        }

        if (
          !map.has(
            seat.time
          )
        ) {
          map.set(
            seat.time,
            {
              label:
                seat.time,

              start:
                seat.start,

              end:
                seat.end,

              startText:
                seat.time
                  .split('-')[0]
            }
          );
        }
      }
    );

    return [
      ...map.values()
    ]
      .filter(
        x =>
          x.start !== null
      )
      .sort(
        (a, b) =>
          a.start -
          b.start
      );
  }

  function chooseTimes(times) {
    if (!times.length) {
      return [];
    }

    checkManualTimeout();

    const now =
      nowMinutes();

    let index = 0;

    if (
      manualStart !== null
    ) {
      const i =
        times.findIndex(
          x =>
            x.start >=
            manualStart
        );

      index =
        i >= 0
          ? i
          : times.length - 1;

    } else {
      const current =
        times.findIndex(
          x =>
            now >= x.start &&
            now <= x.end
        );

      if (
        current >= 0
      ) {
        index = current;

      } else {
        const next =
          times.findIndex(
            x =>
              x.start > now
          );

        index =
          next >= 0
            ? next
            : Math.max(
                0,
                times.length - 1
              );
      }
    }

    return times.slice(
      index,
      index + 2
    );
  }

  function fillTimeSelect(
    times
  ) {
    const select =
      document.getElementById(
        'ray-time-select'
      );

    if (!select) {
      return;
    }

    select.innerHTML = '';

    times.forEach(t => {
      const op =
        document.createElement(
          'option'
        );

      op.value =
        t.start;

      op.textContent =
        t.startText;

      select.appendChild(
        op
      );
    });
  }


  // =====================================================
  // BOOTH HTML
  // =====================================================

  function boothHTML(seat) {
    const students =
      seat.students?.length
        ? seat.students
            .map(s => {
              const level =
                getSchoolLevel(
                  s.name
                );

              const entryBadge =
                getStudentEntryBadge(
                  s.name
                );

              return `
                <div
                  class="ray-student ray-${level}"
                  data-ray-name="${esc(s.name || '')}"
                  data-ray-subject="${esc(s.subject || '')}"
                  data-ray-absence="${esc(s.absence || '')}"
                  data-ray-reflection="${esc(s.reflection || '')}"
                  data-ray-student-id="${esc(s.studentId || '')}"
                  data-ray-seat-student-id="${esc(s.seatStudentId || '')}"
                  data-ray-entry="${esc(entryBadge || '')}">

                  <span class="ray-student-name">
                    ${esc(s.name)}
                  </span>

                  ${
                    entryBadge
                      ? `
                        <span
                          class="ray-entry-badge ${
                            entryBadge === '初回'
                              ? 'ray-first'
                              : 'ray-new'
                          }">
                          ${esc(entryBadge)}
                        </span>
                      `
                      : ''
                  }

                  ${
                    s.subject
                      ? `
                        <span class="ray-subject">
                          ${esc(s.subject)}
                        </span>
                      `
                      : ''
                  }

                  ${
                    s.absence
                      ? `
                        <span class="ray-extra ray-absence">
                          ${esc(s.absence)}
                        </span>
                      `
                      : ''
                  }

                  ${
                    s.reflection
                      ? `
                        <span class="ray-extra ray-reflection">
                          ${esc(s.reflection)}
                        </span>
                      `
                      : ''
                  }

                </div>
              `;
            })
            .join('')

        : `
            <div class="ray-empty-seat">
              生徒なし
            </div>
          `;

    return `
      <div class="ray-booth">

        <div class="ray-booth-head">

          <span>
            ${esc(seat.booth)}
          </span>

          <span class="ray-count">
            ${esc(
              seat.count ||
              ''
            )}
          </span>

        </div>

        <div class="ray-teacher">
          講師 ${
            esc(
              seat.teacher ||
              '未設定'
            )
          }
        </div>

        ${students}

      </div>
    `;
  }


  // =====================================================
  // TIME COLUMN
  // =====================================================

  // =====================================================
  // v8.7.3 ROOM ROW RESIZER
  // ①②番教室 / ③④番教室の境界を上下ドラッグ。
  // 全時間列で同じ比率を使い、ブラウザに保存する。
  // =====================================================

  const ROOM_SPLIT_STORAGE_KEY =
    'RAYS_ROOM_SPLIT_V87';

  function savedRoomSplit() {
    const raw =
      Number(
        localStorage.getItem(
          ROOM_SPLIT_STORAGE_KEY
        )
      );

    return (
      Number.isFinite(raw) &&
      raw >= 25 &&
      raw <= 75
    )
      ? raw
      : 50;
  }

  function applyRoomSplit(percent) {
    const value =
      Math.max(
        25,
        Math.min(
          75,
          Number(percent) || 50
        )
      );

    /*
      v8.7.3:
      各時間列(.ray-rooms)へ個別設定するのをやめ、
      documentElement に1個だけ持たせる。
      CSSカスタムプロパティは新しく再生成された右列にも継承されるため、
      数秒後の座席データ再描画で右列だけ初期値へ戻らない。
    */
    document.documentElement.style.setProperty(
      '--ray-upper-fr',
      `${value}fr`
    );

    document.documentElement.style.setProperty(
      '--ray-lower-fr',
      `${100 - value}fr`
    );

    return value;
  }

  // 再描画より先に共通値をルートへ設定。
  // 以後、新しく作られる左右どちらの時間列も必ずこの値を継承する。
  applyRoomSplit(
    savedRoomSplit()
  );


  function installRoomDivider(
    rooms
  ) {
    if (!rooms) return;

    applyRoomSplit(
      savedRoomSplit()
    );

    const divider =
      document.createElement(
        'div'
      );

    divider.className =
      'ray-room-divider';

    divider.title =
      'ドラッグして①②番教室と③④番教室の高さを調整';

    divider.setAttribute(
      'role',
      'separator'
    );

    divider.setAttribute(
      'aria-orientation',
      'horizontal'
    );

    rooms.appendChild(
      divider
    );

    divider.addEventListener(
      'pointerdown',
      event => {
        event.preventDefault();

        divider.classList.add(
          'ray-dragging'
        );

        divider.setPointerCapture(
          event.pointerId
        );
      }
    );

    divider.addEventListener(
      'pointermove',
      event => {
        if (
          !divider.hasPointerCapture(
            event.pointerId
          )
        ) {
          return;
        }

        const rect =
          rooms.getBoundingClientRect();

        if (!rect.height) return;

        const percent =
          (
            (
              event.clientY -
              rect.top
            ) /
            rect.height
          ) * 100;

        const value =
          applyRoomSplit(
            percent
          );

        /*
          v8.7.1:
          自動再描画がドラッグ中に走っても戻らないよう、
          pointermove のたびに最新値を即保存する。
        */
        localStorage.setItem(
          ROOM_SPLIT_STORAGE_KEY,
          String(value)
        );
      }
    );

    const finishDrag =
      event => {
        if (
          divider.hasPointerCapture(
            event.pointerId
          )
        ) {
          divider.releasePointerCapture(
            event.pointerId
          );
        }

        divider.classList.remove(
          'ray-dragging'
        );

        const current =
          parseFloat(
            getComputedStyle(
              document.documentElement
            )
              .getPropertyValue(
                '--ray-upper-fr'
              )
          ) || 50;

        localStorage.setItem(
          ROOM_SPLIT_STORAGE_KEY,
          String(current)
        );
      };

    divider.addEventListener(
      'pointerup',
      finishDrag
    );

    divider.addEventListener(
      'pointercancel',
      finishDrag
    );
  }


  function makeTimeColumn(
    time
  ) {
    const column =
      document.createElement(
        'section'
      );

    column.className =
      'ray-time-column';

    const now =
      nowMinutes();

    const isCurrent =
      (
        now >= time.start &&
        now <= time.end
      );

    column.innerHTML = `
      <div class="ray-time-head">

        ${esc(time.label)}

        ${
          isCurrent
            ? `
              <span class="ray-current">
                現在
              </span>
            `
            : ''
        }

      </div>

      <div class="ray-rooms"></div>
    `;

    const rooms =
      column.querySelector(
        '.ray-rooms'
      );

    const allSeats =
      [
        ...seatCache.values()
      ]
        .filter(
          s =>
            s.time ===
            time.label
        );

    /*
      配置順固定

      ① ②
      ③ ④
    */

    [1, 2, 3, 4]
      .forEach(
        roomNo => {

          const room =
            document.createElement(
              'div'
            );

          room.className =
            `ray-room room-${roomNo}`;

          const mark =
            [
              '',
              '①',
              '②',
              '③',
              '④'
            ][roomNo];

          room.innerHTML = `
            <div class="ray-room-head">
              ${mark}番教室
            </div>

            <div class="ray-room-body"></div>
          `;

          const body =
            room.querySelector(
              '.ray-room-body'
            );

          const seats =
            allSeats
              .filter(
                s =>
                  classroomNumber(
                    s.booth
                  ) ===
                  roomNo
              )
              .sort(
                (a, b) =>
                  boothNumber(
                    a.booth
                  ) -
                  boothNumber(
                    b.booth
                  )
              );

          if (
            !seats.length
          ) {
            body.innerHTML = `
              <div class="ray-empty-seat">
                登録なし
              </div>
            `;

          } else {
            body.innerHTML =
              seats
                .map(
                  boothHTML
                )
                .join('');
          }

          rooms.appendChild(
            room
          );
        }
      );

    installRoomDivider(
      rooms
    );

    return column;
  }


  // =====================================================
  // RENDER
  // =====================================================

  function render() {
    if (!IS_RAY_SEAT_PAGE) return;
    checkManualTimeout();

    const times =
      getAllTimes();

    fillTimeSelect(
      times
    );

    const selected =
      chooseTimes(
        times
      );

    const box =
      document.getElementById(
        'ray-two-columns'
      );

    if (!box) {
      return;
    }

    box.innerHTML = '';

    if (
      !selected.length
    ) {
      box.innerHTML = `
        <div class="ray-no-data">
          座席情報を取得できていません。
        </div>
      `;

      return;
    }

    const select =
      document.getElementById(
        'ray-time-select'
      );

    if (
      select &&
      selected[0]
    ) {
      select.value =
        String(
          selected[0].start
        );
    }

    selected.forEach(
      time => {
        box.appendChild(
          makeTimeColumn(
            time
          )
        );
      }
    );

    if (
      selected.length === 1
    ) {
      const blank =
        document.createElement(
          'section'
        );

      blank.className =
        'ray-time-column';

      blank.innerHTML = `
        <div class="ray-time-head">
          次のコマなし
        </div>

        <div class="ray-no-data">
          表示する次コマはありません
        </div>
      `;

      box.appendChild(
        blank
      );
    }

    updateScanStatus();
  }


  // =====================================================
  // v6.1
  // 専用モニター上の講師・生徒をクリックして
  // Comiru標準の「更新」編集欄を呼び出す
  // =====================================================

  function normalizeForMatch(v) {
    return clean(v)
      .replace(/[（(][^）)]*[）)]/g, '')
      .replace(/\s+/g, '');
  }

  function visibleElement(el) {
    if (!el) return false;

    const style = getComputedStyle(el);
    const rect = el.getBoundingClientRect();

    return (
      style.display !== 'none' &&
      style.visibility !== 'hidden' &&
      rect.width > 0 &&
      rect.height > 0
    );
  }

  function findUpdateButtonFromNode(node) {
    let cur = node;

    for (let i = 0; cur && i < 12; i++, cur = cur.parentElement) {
      const buttons = [
        ...cur.querySelectorAll(
          'button, a, [role="button"], input[type="button"], input[type="submit"]'
        )
      ];

      const update = buttons.find(btn => {
        const label = clean(
          btn.textContent ||
          btn.value ||
          btn.getAttribute('aria-label') ||
          ''
        );

        return visibleElement(btn) && label === '更新';
      });

      if (update) {
        return update;
      }
    }

    return null;
  }

  async function openComiruEditorByText(label) {
    const target = normalizeForMatch(label);

    if (!target) {
      showComiru();
      return;
    }

    showComiru();

    await sleep(250);

    const candidates = [
      ...document.querySelectorAll(
        'span, div, p, td, th, label, a, button'
      )
    ]
      .filter(el => {
        if (
          el.closest('#ray-header') ||
          el.closest('#ray-sidebar') ||
          el.closest('#ray-monitor') ||
          el.closest('#ray-return')
        ) {
          return false;
        }

        if (!visibleElement(el)) {
          return false;
        }

        const value = normalizeForMatch(el.textContent);

        return (
          value === target ||
          (
            target.length >= 2 &&
            value.includes(target) &&
            value.length <= target.length + 12
          )
        );
      })
      .sort((a, b) => {
        const av = normalizeForMatch(a.textContent);
        const bv = normalizeForMatch(b.textContent);

        return (
          Math.abs(av.length - target.length) -
          Math.abs(bv.length - target.length)
        );
      });

    for (const node of candidates) {
      const update = findUpdateButtonFromNode(node);

      if (!update) {
        continue;
      }

      node.scrollIntoView({
        behavior:'smooth',
        block:'center',
        inline:'center'
      });

      await sleep(250);

      update.click();

      return;
    }

    /*
      Comiru側DOMの都合で対象を直接特定できなかった場合も、
      標準画面は開いたままにする。
      誤った座席の「更新」は押さない。
    */
    console.warn(
      '[RAYS v6.5] 対象の更新ボタンを特定できませんでした:',
      label
    );
  }

  // =====================================================
  // v7.3 COMIRU STUDENT DETAIL / SCORES
  // =====================================================

  function compactLines(text) {
    return String(text || '')
      .split(/\r?\n/)
      .map(v => clean(v))
      .filter(Boolean);
  }

  function findLabeledValue(doc, labels) {
    const wanted =
      labels.map(
        v => clean(v)
      );

    const rows =
      Array.from(
        doc.querySelectorAll(
          'tr'
        )
      );

    for (const row of rows) {
      const cells =
        Array.from(
          row.querySelectorAll(
            'th,td'
          )
        );

      if (cells.length < 2) {
        continue;
      }

      const key =
        clean(
          cells[0].textContent
        );

      if (
        wanted.some(
          label =>
            key === label ||
            key.includes(label)
        )
      ) {
        return clean(
          cells
            .slice(1)
            .map(
              cell =>
                cell.textContent
            )
            .join(' ')
        );
      }
    }

    return '';
  }

  function findSectionText(doc, labels) {
    const nodes =
      Array.from(
        doc.querySelectorAll(
          'th,td,dt,dd,h1,h2,h3,h4,label,div'
        )
      );

    for (const node of nodes) {
      const t =
        clean(
          node.textContent
        );

      const label =
        labels.find(
          v =>
            t === v ||
            t.startsWith(
              `${v} `
            )
        );

      if (!label) {
        continue;
      }

      if (
        node.tagName === 'TH' ||
        node.tagName === 'TD'
      ) {
        const row =
          node.closest('tr');

        if (row) {
          const cells =
            Array.from(
              row.querySelectorAll(
                'th,td'
              )
            );

          if (cells.length >= 2) {
            const value =
              clean(
                cells
                  .slice(1)
                  .map(
                    cell =>
                      cell.textContent
                  )
                  .join(' ')
              );

            if (value) {
              return value;
            }
          }
        }
      }

      const next =
        node.nextElementSibling;

      if (next) {
        const value =
          clean(
            next.textContent
          );

        if (
          value &&
          value !== t
        ) {
          return value;
        }
      }
    }

    return '';
  }

  function deriveTeachingInfo(noteText) {
    const lines =
      compactLines(
        noteText
      );

    const materialWords = [
      '教材',
      'テキスト',
      '新中問',
      '必修',
      'WINPASS',
      'ウィンパス',
      '論理エンジン',
      'フォレスタ',
      'FS',
      'ワーク'
    ];

    const pointWords = [
      '指導',
      '課題',
      '苦手',
      '重点',
      '注意',
      '目標',
      '復習',
      '確認'
    ];

    const materials =
      lines
        .filter(
          line =>
            materialWords.some(
              word =>
                line.includes(word)
            )
        )
        .slice(0, 3);

    const points =
      lines
        .filter(
          line =>
            pointWords.some(
              word =>
                line.includes(word)
            )
        )
        .slice(0, 3);

    return {
      materials:
        materials.join(' / '),
      points:
        points.join(' / ')
    };
  }

  async function fetchHtmlDocument(url) {
    const response =
      await fetch(
        url,
        {
          credentials:
            'include',
          cache:
            'no-store'
        }
      );

    if (!response.ok) {
      throw new Error(
        `HTTP ${response.status}`
      );
    }

    const html =
      await response.text();

    return new DOMParser()
      .parseFromString(
        html,
        'text/html'
      );
  }

  // =====================================================
  // v7.6 COMIRU STUDENT DIRECTORY CACHE
  // 生徒一覧で実際に表示された S_xxxxx リンクを保存する
  // =====================================================

  const RAY_STUDENT_DIRECTORY_KEY =
    'RAYS_COMIRU_STUDENT_DIRECTORY_V76';

  function loadSavedStudentDirectory() {
    try {
      const raw =
        localStorage.getItem(
          RAY_STUDENT_DIRECTORY_KEY
        );

      const parsed =
        raw
          ? JSON.parse(raw)
          : [];

      return Array.isArray(parsed)
        ? parsed
        : [];
    } catch (error) {
      return [];
    }
  }

  function saveStudentDirectoryEntry(
    studentName,
    href
  ) {
    const normalized =
      normalizeStudentName(
        studentName
      );

    if (
      !normalized ||
      !href ||
      !isStudentDetailHref(
        href
      )
    ) {
      return;
    }

    const list =
      loadSavedStudentDirectory();

    const filtered =
      list.filter(
        item =>
          item &&
          item.normalized !==
            normalized
      );

    filtered.push({
      name:
        clean(
          studentName
        ),
      normalized,
      href,
      savedAt:
        Date.now()
    });

    localStorage.setItem(
      RAY_STUDENT_DIRECTORY_KEY,
      JSON.stringify(
        filtered.slice(-500)
      )
    );
  }

  function scanVisibleComiruStudentLinks() {
    const links =
      Array.from(
        document.querySelectorAll(
          'a[href*="/student/S_"]'
        )
      );

    for (const link of links) {
      const href =
        absoluteComiruUrl(
          link.getAttribute(
            'href'
          )
        );

      const name =
        clean(
          link.textContent
        );

      if (
        href &&
        name
      ) {
        saveStudentDirectoryEntry(
          name,
          href
        );
      }
    }
  }

  function clickShowAllStudentsV78() {
    const button =
      Array.from(
        document.querySelectorAll('a,button')
      )
      .find(
        el =>
          clean(el.textContent) ===
          'すべて表示する'
      );

    if (!button) {
      return false;
    }

    try {
      button.click();
      return true;
    } catch (error) {
      console.warn(
        '[RAYS v8.0] すべて表示する自動クリック失敗',
        error
      );
      return false;
    }
  }

  function installComiruStudentDirectoryScanner() {
    if (!IS_RAY_STUDENT_LIST_PAGE) {
      return;
    }

    /*
      Comiru標準画面は一切隠さない・置換しない。
      表示された生徒名と /student/S_xxxxx の対応だけ保存。
    */
    const scan = () => {
      scanVisibleComiruStudentLinks();

      console.log(
        `[RAYS v8.0] 生徒URL保存数: ${
          loadSavedStudentDirectory().length
        }`
      );
    };

    scan();

    setTimeout(
      () => {
        clickShowAllStudentsV78();
        scan();
      },
      500
    );

    setTimeout(scan, 1500);
    setTimeout(scan, 3000);
    setTimeout(scan, 5000);

    const observer =
      new MutationObserver(
        () => {
          scanVisibleComiruStudentLinks();
        }
      );

    observer.observe(
      document.documentElement,
      {
        childList:true,
        subtree:true
      }
    );
  }

  function absoluteComiruUrl(href) {
    try {
      return new URL(
        href,
        location.origin
      ).href;
    } catch (error) {
      return '';
    }
  }

  function isStudentDetailHref(href) {
    return /\/ray-school(?:_ekinan)?\/student\/S_[A-Za-z0-9_-]+(?:[/?#]|$)/
      .test(
        String(
          href || ''
        )
      );
  }

  function extractStudentLinksFromDocument(doc) {
    const result = [];

    const links =
      Array.from(
        doc.querySelectorAll(
          'a[href]'
        )
      );

    for (const link of links) {
      const href =
        absoluteComiruUrl(
          link.getAttribute(
            'href'
          )
        );

      if (
        !isStudentDetailHref(
          href
        )
      ) {
        continue;
      }

      const row =
        link.closest(
          'tr,li,.card,.list-group-item'
        );

      const linkText =
        clean(
          link.textContent
        );

      const rowText =
        clean(
          row
            ? row.textContent
            : ''
        );

      result.push({
        href,
        nameText:
          linkText,
        contextText:
          rowText
      });
    }

    return result;
  }

  function mergeStudentLinks(
    map,
    links
  ) {
    for (const item of links) {
      const href =
        item.href;

      if (!href) {
        continue;
      }

      const candidates = [
        item.nameText,
        item.contextText
      ];

      for (const candidate of candidates) {
        const normalized =
          normalizeStudentName(
            candidate
          );

        if (!normalized) {
          continue;
        }

        /*
          行全体の文字列は学校名なども含むため、
          完全一致用ではなく「名前を含む候補」として保持。
        */
        if (
          !map.some(
            saved =>
              saved.href === href &&
              saved.normalized === normalized
          )
        ) {
          map.push({
            href,
            normalized,
            raw:
              candidate
          });
        }
      }
    }
  }

  async function buildComiruStudentDirectory() {
    if (
      comiruStudentDirectoryPromise
    ) {
      return comiruStudentDirectoryPromise;
    }

    comiruStudentDirectoryPromise =
      (async () => {
        const directory = [];

        /*
          Comiruの画面構成差に対応するため、
          生徒一覧として使われる可能性のあるURLを順番に確認。
          ログイン中のCookieをそのまま利用する。
        */
        const schoolBase =
          `${location.origin}/${COMIRU_SCHOOL_SLUG}`;

        const candidateUrls = [
          `${schoolBase}/student`,
          `${schoolBase}/student/`,
          `${schoolBase}/students`,
          `${schoolBase}/students/`
        ];

        for (const url of candidateUrls) {
          try {
            const doc =
              await fetchHtmlDocument(
                url
              );

            const links =
              extractStudentLinksFromDocument(
                doc
              );

            if (links.length) {
              mergeStudentLinks(
                directory,
                links
              );

              /*
                一覧ページにページネーションがある場合、
                同一画面内の次ページ候補も最大20ページまで読む。
              */
              const pageLinks =
                Array.from(
                  doc.querySelectorAll(
                    'a[href]'
                  )
                )
                .map(
                  a =>
                    absoluteComiruUrl(
                      a.getAttribute(
                        'href'
                      )
                    )
                )
                .filter(
                  href =>
                    href &&
                    href.startsWith(
                      location.origin
                    ) &&
                    (
                      href.includes(
                        `/${COMIRU_SCHOOL_SLUG}/student`
                      ) ||
                      href.includes(
                        `/${COMIRU_SCHOOL_SLUG}/students`
                      )
                    ) &&
                    (
                      /[?&]page=\d+/i.test(
                        href
                      ) ||
                      /\/page\/\d+/i.test(
                        href
                      )
                    )
                );

              const uniquePages =
                Array.from(
                  new Set(
                    pageLinks
                  )
                )
                .slice(
                  0,
                  20
                );

              for (
                const pageUrl
                of uniquePages
              ) {
                try {
                  const pageDoc =
                    await fetchHtmlDocument(
                      pageUrl
                    );

                  mergeStudentLinks(
                    directory,
                    extractStudentLinksFromDocument(
                      pageDoc
                    )
                  );
                } catch (error) {
                  console.warn(
                    '[RAYS v8.0] 生徒一覧ページ取得失敗',
                    pageUrl,
                    error
                  );
                }
              }

              break;
            }
          } catch (error) {
            console.warn(
              '[RAYS v8.0] 生徒一覧候補取得失敗',
              url,
              error
            );
          }
        }

        return directory;
      })();

    return comiruStudentDirectoryPromise;
  }

  function scoreStudentDirectoryCandidate(
    candidate,
    studentName
  ) {
    const target =
      normalizeStudentName(
        studentName
      );

    const saved =
      candidate.normalized ||
      '';

    if (
      !target ||
      !saved
    ) {
      return 0;
    }

    if (
      saved === target
    ) {
      return 100;
    }

    if (
      saved.startsWith(
        target
      ) ||
      saved.endsWith(
        target
      )
    ) {
      return 90;
    }

    if (
      saved.includes(
        target
      )
    ) {
      return 80;
    }

    if (
      target.includes(
        saved
      ) &&
      saved.length >= 3
    ) {
      return 60;
    }

    return 0;
  }

  async function findStudentDetailUrlByName(
    studentName
  ) {
    /*
      v7.6:
      生徒一覧で実際に表示されたリンクを最優先。
      座席管理の数値IDと S_xxxxx を推測で結ばない。
    */
    const targetName =
      normalizeStudentName(
        studentName
      );

    const savedDirectory =
      loadSavedStudentDirectory();

    const savedExact =
      savedDirectory.find(
        item =>
          item &&
          item.normalized ===
            targetName &&
          isStudentDetailHref(
            item.href
          )
      );

    if (savedExact) {
      return savedExact.href;
    }

    /*
      まず現在DOM内に詳細リンクがあれば最優先。
    */
    const currentLinks =
      extractStudentLinksFromDocument(
        document
      );

    const currentCandidates = [];

    mergeStudentLinks(
      currentCandidates,
      currentLinks
    );

    let best = null;

    for (
      const candidate
      of currentCandidates
    ) {
      const score =
        scoreStudentDirectoryCandidate(
          candidate,
          studentName
        );

      if (
        !best ||
        score >
        best.score
      ) {
        best = {
          ...candidate,
          score
        };
      }
    }

    if (
      best &&
      best.score >= 80
    ) {
      return best.href;
    }

    /*
      座席画面には詳細リンクが無いので、
      Comiru生徒一覧を裏で取得して氏名照合する。
    */
    const directory =
      await buildComiruStudentDirectory();

    best = null;

    for (
      const candidate
      of directory
    ) {
      const score =
        scoreStudentDirectoryCandidate(
          candidate,
          studentName
        );

      if (
        !best ||
        score >
        best.score
      ) {
        best = {
          ...candidate,
          score
        };
      }
    }

    if (
      best &&
      best.score >= 80
    ) {
      return best.href;
    }

    return '';
  }

  async function loadStudentDetail(
    studentId,
    studentName
  ) {
    const cacheKey =
      [
        studentId || '',
        normalizeStudentName(
          studentName
        )
      ].join('|');

    if (
      studentDetailCache.has(
        cacheKey
      )
    ) {
      return studentDetailCache.get(
        cacheKey
      );
    }

    const promise =
      (async () => {
        const detailUrl =
          await findStudentDetailUrlByName(
            studentName
          );

        if (!detailUrl) {
          return {
            school: '',
            grade: '',
            note: '',
            materials: '',
            points: '',
            detailUrl: '',
            directoryMatched:
              false
          };
        }

        const doc =
          await fetchHtmlDocument(
            detailUrl
          );

        /*
          実際のComiru生徒詳細では
          「学校情報」「学年」が表形式で表示される。
        */
        const school =
          findLabeledValue(
            doc,
            [
              '学校情報',
              '学校',
              '学校名',
              '在籍校',
              '所属学校'
            ]
          ) ||
          findSectionText(
            doc,
            [
              '学校情報',
              '学校',
              '学校名',
              '在籍校',
              '所属学校'
            ]
          );

        const grade =
          findLabeledValue(
            doc,
            [
              '学年'
            ]
          ) ||
          findSectionText(
            doc,
            [
              '学年'
            ]
          );

        const note =
          findLabeledValue(
            doc,
            [
              'ノート'
            ]
          ) ||
          findSectionText(
            doc,
            [
              'ノート'
            ]
          );

        const derived =
          deriveTeachingInfo(
            note
          );

        return {
          school,
          grade,
          note,
          materials:
            derived.materials,
          points:
            derived.points,
          detailUrl,
          directoryMatched:
            true
        };
      })()
      .catch(
        error => ({
          school: '',
          grade: '',
          note: '',
          materials: '',
          points: '',
          detailUrl: '',
          directoryMatched:
            false,
          error:
            String(
              error.message ||
              error
            )
        })
      );

    studentDetailCache.set(
      cacheKey,
      promise
    );

    return promise;
  }

  function parseLatestScores(doc) {
    const rows =
      Array.from(
        doc.querySelectorAll(
          'tr'
        )
      );

    const subjectNames = [
      '国語',
      '社会',
      '数学',
      '英語',
      '理科'
    ];

    for (const row of rows) {
      const text =
        clean(
          row.textContent
        );

      if (
        !text ||
        !subjectNames.some(
          subject =>
            text.includes(
              subject
            )
        )
      ) {
        continue;
      }

      const cells =
        Array.from(
          row.querySelectorAll(
            'th,td'
          )
        )
        .map(
          cell =>
            clean(
              cell.textContent
            )
        );

      if (
        cells.length < 5
      ) {
        continue;
      }

      const values = {};

      for (const subject of subjectNames) {
        const index =
          cells.findIndex(
            cell =>
              cell === subject
          );

        if (
          index >= 0 &&
          cells[index + 1]
        ) {
          values[subject] =
            cells[index + 1];
        }
      }

      if (
        Object.keys(
          values
        ).length >= 2
      ) {
        return {
          title:
            cells[0] || '',
          values
        };
      }
    }

    /*
      Comiruの成績一覧は、見出し行とデータ行が
      分離している場合があるため、表単位でも読む。
    */
    const tables =
      Array.from(
        doc.querySelectorAll(
          'table'
        )
      );

    for (const table of tables) {
      const headers =
        Array.from(
          table.querySelectorAll(
            'thead th'
          )
        )
        .map(
          th =>
            clean(
              th.textContent
            )
        );

      if (
        !subjectNames.some(
          subject =>
            headers.includes(
              subject
            )
        )
      ) {
        continue;
      }

      const dataRows =
        Array.from(
          table.querySelectorAll(
            'tbody tr'
          )
        );

      for (const row of dataRows) {
        const cells =
          Array.from(
            row.querySelectorAll(
              'td'
            )
          )
        .map(
          td =>
            clean(
              td.textContent
            )
          );

        if (!cells.length) {
          continue;
        }

        const values = {};

        subjectNames.forEach(
          subject => {
            const index =
              headers.indexOf(
                subject
              );

            if (
              index >= 0 &&
              cells[index] !== undefined
            ) {
              values[subject] =
                cells[index];
            }
          }
        );

        if (
          Object.values(
            values
          ).some(Boolean)
        ) {
          return {
            title:
              cells
                .slice(
                  0,
                  Math.max(
                    1,
                    headers.findIndex(
                      h =>
                        subjectNames.includes(
                          h
                        )
                    )
                  )
                )
                .filter(Boolean)
                .join(' '),
            values
          };
        }
      }
    }

    return null;
  }

  async function loadStudentScores(
    studentId
  ) {
    if (!studentId) {
      return {
        scoreUrl: '',
        latest: null
      };
    }

    if (
      studentScoreCache.has(
        studentId
      )
    ) {
      return studentScoreCache.get(
        studentId
      );
    }

    const promise =
      (async () => {
        const scoreUrl =
          `${location.origin}/ray-school/students/${encodeURIComponent(studentId)}/scores`;

        const doc =
          await fetchHtmlDocument(
            scoreUrl
          );

        return {
          scoreUrl,
          latest:
            parseLatestScores(
              doc
            )
        };
      })()
      .catch(
        error => ({
          scoreUrl:
            `${location.origin}/ray-school/students/${encodeURIComponent(studentId)}/scores`,
          latest: null,
          error:
            String(
              error.message ||
              error
            )
        })
      );

    studentScoreCache.set(
      studentId,
      promise
    );

    return promise;
  }

  function formatScoreLine(
    latest
  ) {
    if (
      !latest ||
      !latest.values
    ) {
      return '成績データを取得できませんでした';
    }

    const order = [
      '国語',
      '数学',
      '英語',
      '理科',
      '社会'
    ];

    return order
      .map(
        subject =>
          `${subject} ${
            latest.values[
              subject
            ] || '―'
          }`
      )
      .join('｜');
  }

  async function enrichStudentCard(
    studentEl,
    card,
    cardToken
  ) {
    const studentId =
      clean(
        studentEl.dataset
          .rayStudentId ||
        studentEl.dataset
          .raySeatStudentId ||
        ''
      );

    const studentName =
      clean(
        studentEl.dataset
          .rayName ||
        studentEl
          .querySelector(
            '.ray-student-name'
          )
          ?.textContent ||
        ''
      );

    if (
      !studentId &&
      !studentName
    ) {
      return;
    }

    /*
      v7.5:
      先に氏名から S_xxxxx の生徒詳細を特定。
      学校・学年・ノートは詳細ページから取得。
      成績は従来の数値ID URLを試しつつ、
      詳細ページから成績リンクを見つけられる場合は
      そちらを優先できるようにする。
    */
    const detail =
      await loadStudentDetail(
        studentId,
        studentName
      );

    let scores =
      await loadStudentScores(
        studentId
      );

    if (
      detail.detailUrl
    ) {
      try {
        const detailDoc =
          await fetchHtmlDocument(
            detail.detailUrl
          );

        const scoreLink =
          Array.from(
            detailDoc.querySelectorAll(
              'a[href]'
            )
          )
          .map(
            a => ({
              href:
                absoluteComiruUrl(
                  a.getAttribute(
                    'href'
                  )
                ),
              text:
                clean(
                  a.textContent
                )
            })
          )
          .find(
            item =>
              item.href &&
              (
                item.href.includes(
                  '/scores'
                ) ||
                item.text.includes(
                  '成績'
                )
              )
          );

        if (
          scoreLink &&
          scoreLink.href
        ) {
          try {
            const scoreDoc =
              await fetchHtmlDocument(
                scoreLink.href
              );

            const latest =
              parseLatestScores(
                scoreDoc
              );

            if (latest) {
              scores = {
                scoreUrl:
                  scoreLink.href,
                latest
              };
            }
          } catch (error) {
            console.warn(
              '[RAYS v8.0] 詳細ページ経由の成績取得失敗',
              error
            );
          }
        }
      } catch (error) {
        console.warn(
          '[RAYS v8.0] 詳細ページ再読込失敗',
          error
        );
      }
    }

    if (
      card.dataset
        .rayToken !==
      cardToken
    ) {
      return;
    }

    const extra =
      card.querySelector(
        '.ray-card-extra'
      );

    if (!extra) {
      return;
    }

    extra.innerHTML = `
      <div class="ray-card-row">
        <div class="ray-card-label">
          学校
        </div>
        <div class="ray-card-value">
          ${esc(
            detail.school ||
            'Comiru生徒一覧で照合できません'
          )}
        </div>
      </div>

      <div class="ray-card-row">
        <div class="ray-card-label">
          学年
        </div>
        <div class="ray-card-value">
          ${esc(
            detail.grade ||
            '未取得'
          )}
        </div>
      </div>

      <div class="ray-card-section">
        <div class="ray-card-section-title">
          教材
        </div>
        <div class="ray-card-value">
          ${
            esc(
              detail.materials ||
              'Comiruノートから特定できません'
            )
          }
        </div>
      </div>

      <div class="ray-card-section">
        <div class="ray-card-section-title">
          指導ポイント
        </div>
        <div class="ray-card-value">
          ${
            esc(
              detail.points ||
              'Comiruノートから特定できません'
            )
          }
        </div>
      </div>

      <div class="ray-card-section">
        <div class="ray-card-section-title">
          直近成績
        </div>
        ${
          scores.latest &&
          scores.latest.title
            ? `
              <div class="ray-card-source">
                ${esc(scores.latest.title)}
              </div>
            `
            : ''
        }
        <div class="ray-card-score">
          ${esc(
            formatScoreLine(
              scores.latest
            )
          )}
        </div>
      </div>

      <div class="ray-card-source">
        Comiruから取得
      </div>

      <div class="ray-realte-block">
        ${realteCardHtml(
          studentName
        )}
      </div>
    `;
  }


  // =====================================================
  // v7.2 STUDENT HOVER CARD
  // =====================================================

  function ensureStudentCard() {
    let card =
      document.getElementById(
        'ray-student-card'
      );

    if (card) {
      return card;
    }

    card =
      document.createElement(
        'div'
      );

    card.id =
      'ray-student-card';

    document.body.appendChild(
      card
    );

    return card;
  }

  function positionStudentCard(
    card,
    clientX,
    clientY
  ) {
    const margin = 14;

    card.style.left =
      '0px';

    card.style.top =
      '0px';

    card.classList.add(
      'ray-show'
    );

    const rect =
      card.getBoundingClientRect();

    let left =
      clientX + 16;

    let top =
      clientY + 16;

    if (
      left +
      rect.width +
      margin >
      window.innerWidth
    ) {
      left =
        clientX -
        rect.width -
        16;
    }

    if (
      top +
      rect.height +
      margin >
      window.innerHeight
    ) {
      top =
        clientY -
        rect.height -
        16;
    }

    left =
      Math.max(
        margin,
        left
      );

    top =
      Math.max(
        margin,
        top
      );

    card.style.left =
      `${left}px`;

    card.style.top =
      `${top}px`;
  }

  function renderStudentCard(
    studentEl,
    clientX,
    clientY
  ) {
    const card =
      ensureStudentCard();

    const name =
      clean(
        studentEl.dataset
          .rayName ||
        studentEl
          .querySelector(
            '.ray-student-name'
          )
          ?.textContent ||
        ''
      );

    const subject =
      clean(
        studentEl.dataset
          .raySubject ||
        ''
      );

    const absence =
      clean(
        studentEl.dataset
          .rayAbsence ||
        ''
      );

    const reflection =
      clean(
        studentEl.dataset
          .rayReflection ||
        ''
      );

    const entry =
      clean(
        studentEl.dataset
          .rayEntry ||
        ''
      );

    const studentId =
      clean(
        studentEl.dataset
          .rayStudentId ||
        ''
      );

    const seatStudentId =
      clean(
        studentEl.dataset
          .raySeatStudentId ||
        ''
      );

    card.innerHTML = `
      <div class="ray-card-head">
        <div class="ray-card-name">
          ${esc(name)}
        </div>

        ${
          entry
            ? `
              <span
                class="ray-card-badge ${
                  entry === '初回'
                    ? 'ray-first'
                    : 'ray-new'
                }">
                ${esc(entry)}
              </span>
            `
            : ''
        }
      </div>

      ${
        reflection
          ? `
            <div class="ray-card-row">
              <div class="ray-card-label">
                指示
              </div>
              <div class="ray-card-value">
                ${esc(reflection)}
              </div>
            </div>
          `
          : ''
      }

      ${
        entry === '初回'
          ? `
            <div class="ray-card-note ray-card-alert">
              初回授業です。教材・指導ポイントを確認してください。
            </div>
          `
          : entry === '新規'
            ? `
              <div class="ray-card-note">
                新規入塾生です。教材・指導ポイントを確認してください。
              </div>
            `
            : ''
      }

      <div class="ray-card-extra">
        <div class="ray-card-section">
          <div class="ray-card-loading">
            Comiruの生徒情報・成績を読込中…
          </div>
        </div>

        <div class="ray-realte-block">
          ${realteCardHtml(
            name
          )}
        </div>
      </div>

      <div class="ray-card-hint">
        クリック：Comiru標準画面でこの生徒を編集
      </div>
    `;

    const cardToken =
      `${Date.now()}-${Math.random()}`;

    card.dataset.rayToken =
      cardToken;

    positionStudentCard(
      card,
      clientX,
      clientY
    );

    ensureRealteAiSummaryForCard(
      name,
      card,
      cardToken
    );

    enrichStudentCard(
      studentEl,
      card,
      cardToken
    ).then(
      function() {
        ensureRealteAiSummaryForCard(
          name,
          card,
          cardToken
        );
      }
    );
  }

  function hideStudentCard() {
    document
      .getElementById(
        'ray-student-card'
      )
      ?.classList
      .remove(
        'ray-show'
      );
  }

  function installStudentHoverCard() {
    document.addEventListener(
      'mouseover',
      event => {
        if (!customMode) {
          return;
        }

        const student =
          event.target.closest(
            '.ray-student'
          );

        if (!student) {
          return;
        }

        if (
          event.relatedTarget &&
          student.contains(
            event.relatedTarget
          )
        ) {
          return;
        }

        renderStudentCard(
          student,
          event.clientX,
          event.clientY
        );
      },
      true
    );

    document.addEventListener(
      'mousemove',
      event => {
        if (!customMode) {
          return;
        }

        const student =
          event.target.closest(
            '.ray-student'
          );

        const card =
          document.getElementById(
            'ray-student-card'
          );

        if (
          !student ||
          !card ||
          !card.classList.contains(
            'ray-show'
          )
        ) {
          return;
        }

        positionStudentCard(
          card,
          event.clientX,
          event.clientY
        );
      },
      true
    );

    document.addEventListener(
      'mouseout',
      event => {
        const student =
          event.target.closest(
            '.ray-student'
          );

        if (!student) {
          return;
        }

        if (
          event.relatedTarget &&
          student.contains(
            event.relatedTarget
          )
        ) {
          return;
        }

        hideStudentCard();
      },
      true
    );
  }


  function installEditDelegation() {
    document.addEventListener(
      'click',
      event => {
        if (!customMode) {
          return;
        }

        const teacher =
          event.target.closest('.ray-teacher');

        const student =
          event.target.closest('.ray-student');

        const target =
          student || teacher;

        if (!target) {
          return;
        }

        event.preventDefault();
        event.stopPropagation();

        let label = '';

        if (student) {
          label = clean(
            student
              .querySelector('.ray-student-name')
              ?.textContent ||
            student.textContent
          );
        } else {
          label = clean(
            teacher.textContent
          );
        }

        openComiruEditorByText(label);
      },
      true
    );
  }


  // =====================================================
  // v6.2
  // Comiru本来の「全て編集」を呼び出し、
  // 左側の「生徒」「講師」配置機能をそのまま使う
  // =====================================================

  function getNativeButtonLabel(el) {
    return clean(
      el?.textContent ||
      el?.value ||
      el?.getAttribute?.('aria-label') ||
      el?.getAttribute?.('title') ||
      ''
    );
  }

  function findNativeAllEditButton() {
    const nodes = [
      ...document.querySelectorAll(
        'button, a, [role="button"], input[type="button"], input[type="submit"]'
      )
    ];

    return nodes.find(el => {
      if (
        el.closest('#ray-header') ||
        el.closest('#ray-sidebar') ||
        el.closest('#ray-monitor') ||
        el.closest('#ray-return')
      ) {
        return false;
      }

      if (!visibleElement(el)) {
        return false;
      }

      return (
        getNativeButtonLabel(el)
          .replace(/\s+/g, '') ===
        '全て編集'
      );
    }) || null;
  }

  async function openComiruPlacementEditor() {
    /*
      v6.4
      「生徒・講師を配置」では「全て編集」を絶対に押さない。
      Comiru標準画面へ切り替えるだけにする。

      個別コマの編集は、v6.1からの
      講師名・生徒名クリック編集を使う。
    */
    showComiru();
  }


  // =====================================================
  // STANDARD COMIRU
  // =====================================================

  function showComiru() {
    customMode = false;

    /*
      v6.5
      Comiru標準画面では、
      RAYSが追加した上部・左側・座席モニターを全部退避。
      「座席モニターに戻る」だけ残す。
      「全て編集」は一切押さない。
    */
    document.body.classList.add(
      'ray-standard-mode'
    );

    document
      .getElementById(
        'ray-return'
      )
      ?.remove();

    const btn =
      document.createElement(
        'button'
      );

    btn.id =
      'ray-return';

    btn.textContent =
      '座席モニターに戻る';

    btn.style.cssText = `
      position:fixed;
      right:20px;
      bottom:20px;

      z-index:2147483647;

      padding:12px 18px;

      border:0;
      border-radius:7px;

      background:#0b2d57;
      color:#fff;

      font-size:14px;
      font-weight:900;

      cursor:pointer;

      box-shadow:0 2px 8px rgba(0,0,0,.25);
    `;

    btn.onclick = () => {
      customMode = true;

      document.body.classList.remove(
        'ray-standard-mode'
      );

      btn.remove();

      captureVisibleSeats();

      updateScanStatus();

      render();
    };

    document.body.appendChild(
      btn
    );
  }


  // =====================================================
  // DAY VIEW
  // =====================================================

  function dayView() {
    try {
      const btn =
        [
          ...document
            .querySelectorAll(
              '.calendar-mode-btn'
            )
        ]
          .find(
            e =>
              e.textContent
                .trim() ===
              '日'
          );

      if (btn) {
        btn.click();
      }

    } catch (e) {
      console.error(
        '[RAYS dayView]',
        e
      );
    }
  }


  // =====================================================
  // PERIODIC CAPTURE
  // =====================================================

  function periodicCapture() {
    if (
      scanning ||
      !customMode
    ) {
      return;
    }

    checkManualTimeout();

    captureVisibleSeats();

    updateScanStatus();

    render();
  }


  // =====================================================
  // v6.0
  // 5 MINUTE COMIRU RELOAD
  // =====================================================

  function startComiruAutoReload() {
    setInterval(
      () => {

        /*
          Comiru標準画面を
          操作中なら更新しない
        */
        if (!customMode) {
          return;
        }

        /*
          全座席取得中なら
          更新しない
        */
        if (scanning) {
          return;
        }

        console.log(
          '[RAYS] 5分経過：Comiru最新データを再取得'
        );

        /*
          Comiruそのものを
          再読み込み。

          再読み込み後、
          Tampermonkeyが再起動して
          scanWholeComiru()を実行する。
        */
        location.reload();

      },

      COMIRU_RELOAD_MS
    );
  }


  // =====================================================
  // START
  // =====================================================

  async function start() {

    /*
      v8.0
      ReaLTEでは画面を変更せず、
      ログイン済みVuexから必要最小限の生徒情報・面談情報だけを
      Tampermonkey共有ストレージへ保存する。
    */
    if (IS_REALTE_PAGE) {
      startRealteCacheSync();
      return;
    }

    /*
      v7.8
      生徒一覧はComiru標準画面をそのまま残し、
      URL対応表の収集だけを行う。
    */
    if (IS_RAY_STUDENT_LIST_PAGE) {
      installComiruStudentDirectoryScanner();

      setTimeout(
        testRealteMatchesOnComiruStudentList,
        1500
      );

      return;
    }

    /*
      ここから下は座席管理ページだけ。
    */
    if (!IS_RAY_SEAT_PAGE) {
      return;
    }

    cleanup();

    addCSS();

    createHeader();

    createSidebar();

    createMain();

    /*
      専用モニター上の講師・生徒クリックで
      Comiru標準編集を呼び出す
    */
    installEditDelegation();
    installStudentHoverCard();

    /*
      起動直後に標語等を取得
    */
    fetchSidebar();

    /*
      標語・COUNTDOWN・イベントは
      1分ごとに更新。

      ページ全体はリロードしない。
    */
    setInterval(
      fetchSidebar,
      DATA_REFRESH_MS
    );

    /*
      更新時刻表示
    */
    setInterval(
      updateClock,
      10000
    );

    await sleep(900);

    /*
      Comiruを日表示へ
    */
    dayView();

    /*
      Comiru描画待ち
    */
    await sleep(2500);

    /*
      起動直後
      全座席取得
    */
    await scanWholeComiru();

    /*
      10秒ごと

      ・DOM確認
      ・現在時間帯追従
      ・手動表示の5分復帰判定
    */
    setInterval(
      periodicCapture,
      DOM_CAPTURE_MS
    );

    /*
      v6.0

      Comiruページ全体は
      5分ごとに再読み込み
    */
    startComiruAutoReload();

    console.log(
      `[RAYS] Monitor v${VERSION}`
    );
  }


  if (
    document.readyState ===
    'loading'
  ) {
    document.addEventListener(
      'DOMContentLoaded',
      start,
      {
        once:true
      }
    );

  } else {
    start();
  }

})();